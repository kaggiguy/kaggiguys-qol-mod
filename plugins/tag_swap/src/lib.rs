#![feature(proc_macro_hygiene)]

// tag_swap
//
// Change a player's name tag in the middle of an offline match, together with that tag's saved
// controller settings (button mapping, tap jump, and so on).
//
//   Hold two shoulder buttons (L+R, ZL+ZR, or the SL+SR rail buttons on a sideways Joy-Con)
//   and press  D-pad Right / X   -> next tag
//              D-pad Left  / Y   -> previous tag
//
// It works during play and while the game is paused. The change applies to the player whose
// controller you pressed (controller port 1 = player 1, and so on). The name plates (above the
// fighter and next to the damage) are rewritten, and that tag's controller settings are copied
// into the game's live per-player settings, which the game reads every frame.
//
// How it works (all verified with the tag_probe plugin on game version 13.0.4):
//  * the game keeps the saved tags in a table (name, controller settings) and a live copy of the
//    controller settings for each player;
//  * the name plates are set by one text function, which this plugin watches so it knows which text
//    panes belong to which tag name during a match;
//  * a function that stores a player's tag number is watched so the plugin knows who has which tag.
//
// Which player a controller belongs to is NOT the controller's port: the game numbers players in the
// order they join character select. The plugin learns the pairing at character select (the controller
// that pressed a button just before a slot's tag was set), and for a controller it never saw join it
// works the answer out from the players that are left (see controller_to_player).
// Log: sd:/tag_swap_log.txt

use skyline::hooks::{getRegionAddress, Region};
use skyline::nn::hid::{NpadGcState, NpadHandheldState};
use skyline::nn::ro::LookupSymbol;
use smash::app::{self, lua_bind::*};
use std::ffi::c_void;
use std::fs::OpenOptions;
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

// ---- Buttons ---------------------------------------------------------------------------------
const KEY_X: u64 = 1 << 2;
const KEY_Y: u64 = 1 << 3;
const KEY_LEFT: u64 = 1 << 12;
const KEY_RIGHT: u64 = 1 << 14;
// L, R, ZL, ZR and the four SL/SR rail buttons of the Joy-Cons
const SHOULDER_MASK: u64 = (0xF << 6) | (0xF << 24);
const NEXT_KEYS: u64 = KEY_RIGHT | KEY_X;
const PREV_KEYS: u64 = KEY_LEFT | KEY_Y;

const KIND_NAMES: [&str; 6] = [
    "FullKey (Pro Controller)",
    "Handheld",
    "JoyDual (two Joy-Cons)",
    "JoyLeft",
    "JoyRight",
    "GameCube",
];
const SYMBOLS: [&str; 6] = [
    "_ZN2nn3hid12GetNpadStateEPNS0_16NpadFullKeyStateERKj\0",
    "_ZN2nn3hid12GetNpadStateEPNS0_17NpadHandheldStateERKj\0",
    "_ZN2nn3hid12GetNpadStateEPNS0_16NpadJoyDualStateERKj\0",
    "_ZN2nn3hid12GetNpadStateEPNS0_16NpadJoyLeftStateERKj\0",
    "_ZN2nn3hid12GetNpadStateEPNS0_17NpadJoyRightStateERKj\0",
    "_ZN2nn3hid12GetNpadStateEPNS0_11NpadGcStateERKj\0",
];

extern "C" {
    fn A64HookFunction(symbol: *const c_void, replace: *const c_void, result: *mut *mut c_void);
}

// ---- Game addresses (game version 13.0.4) ----------------------------------------------------
const GHIDRA_BASE: usize = 0x7100000000;
const TAGSET_FN: usize = 0x71019fd0b0; // stores a player's tag number (character-select name pane)
const TEXTSET_FN: usize = 0x71037a1cc0; // writes UTF-16 text into a UI text pane

// Data addresses are those of HewDraw Remix, shifted by the difference between its game-state
// global and ours (-0x1000 on this game version). The plugin refuses to run on any other shift.
const HDR_GAME_STATE_GLOBAL: i64 = 0x52c3760;
const EXPECTED_SHIFT: i64 = -0x1000;
const PATTERN: [u8; 32] = [
    0xf5, 0x0f, 0x1d, 0xf8, 0xf4, 0x4f, 0x01, 0xa9, 0xfd, 0x7b, 0x02, 0xa9, 0xfd, 0x83, 0x00, 0x91,
    0x08, 0x14, 0x40, 0xb9, 0xf4, 0x03, 0x01, 0xaa, 0xf3, 0x03, 0x00, 0xaa, 0x1f, 0x05, 0x00, 0x71,
];
const ADRP_AFTER_PATTERN: usize = 0x28;

const TAG_GLOBAL: usize = 0x5314510; // text base + this (+shift): pointer chain to the first tag record
const TAG_SIZE: usize = 0xF7D8;
const TAG_NAME_LEN: usize = 0x8;
const TAG_NAME: usize = 0xC;
const TAG_MAP: usize = 0x24;
const MAP_SIZE: usize = 0x50;
const MAP_COPY: usize = 0x2c; // the part of the settings that is the real configuration
const LIVE_GLOBAL: usize = 0x52c50f0;
const LIVE_ARRAY: usize = 0x18;
const MAX_TAG: usize = 60;
const PLAYERS: usize = 8;

// ---- Shared state ----------------------------------------------------------------------------
const NULLPTR: AtomicPtr<c_void> = AtomicPtr::new(std::ptr::null_mut());
static ORIG: [AtomicPtr<c_void>; 6] = [NULLPTR; 6];
static ORIG_TAGSET: AtomicPtr<c_void> = AtomicPtr::new(std::ptr::null_mut());
static ORIG_TEXT: AtomicPtr<c_void> = AtomicPtr::new(std::ptr::null_mut());
const Z64: AtomicU64 = AtomicU64::new(0);
static PREV: [AtomicU64; 384] = [Z64; 384];
const Z32: AtomicU32 = AtomicU32::new(0);
static SLOT_TAG: [AtomicU32; PLAYERS] = [Z32; PLAYERS]; // newest tag the game assigned to each player slot
static CUR_TAG: [AtomicU32; PLAYERS] = [Z32; PLAYERS]; // tag each player has right now (changed by us)
static CMD: AtomicU32 = AtomicU32::new(0); // (player << 8) | direction (1 next, 2 previous); 0 = none
static LAST_CMD_MS: AtomicU64 = AtomicU64::new(0);
// Which controller each player slot uses, learned at character select: the controller that pressed a
// button just before the game set that slot's tag (the tag is set when a player joins or changes it).
// Stored as controller id + 1; 0 = unknown.
static SLOT_CTRL: [AtomicU32; PLAYERS] = [Z32; PLAYERS];
static LAST_PRESS_ID: AtomicU32 = AtomicU32::new(0); // controller id + 1 of the newest button press
static LAST_PRESS_MS: AtomicU64 = AtomicU64::new(0);
// Burst detection: one button press can be followed by the game setting the tags of SEVERAL slots in a
// row (character select opening or refreshing). A real join sets one slot. So the first slot a press
// stamps is kept only if no second slot follows from the same press.
static STAMP_PRESS_MS: AtomicU64 = AtomicU64::new(u64::MAX);
static STAMP_SLOT: AtomicUsize = AtomicUsize::new(usize::MAX);
static STAMP_BLOCKED: AtomicBool = AtomicBool::new(false);
static SEEN_IDS: AtomicU64 = AtomicU64::new(0); // controller ids that pressed a button at character select
static IN_MATCH: AtomicBool = AtomicBool::new(false);
static FM_ADDR: AtomicUsize = AtomicUsize::new(0);
static NAMES: Mutex<Vec<String>> = Mutex::new(Vec::new());
// (pane, 4th argument, name, the pane's vtable at the time) for each permanent name plate
// plus the player slot that plate belongs to (usize::MAX = could not tell)
static PANES: Mutex<Vec<(usize, usize, String, usize, usize)>> = Mutex::new(Vec::new());
// the name each player's tag has right now
static PNAME: Mutex<Vec<String>> = Mutex::new(Vec::new());
static BASE: AtomicUsize = AtomicUsize::new(0);
const ZUS: AtomicUsize = AtomicUsize::new(0);
static TAGPTR: [AtomicUsize; PLAYERS] = [ZUS; PLAYERS]; // where the game read each slot's tag number from (last seen)
static ORIG_TAG: [AtomicU32; PLAYERS] = [Z32; PLAYERS]; // tag each player had when the match began
static SUBST_ACTIVE: AtomicBool = AtomicBool::new(false);
// true only while a match or the results screen is up (so the swap never touches character select)
static SUBST_TEXT: AtomicBool = AtomicBool::new(false);
// Where the game keeps its remembered "last tag picked" byte for each player (a fixed spot in the
// game's own data, 0x240 apart per player). Character select reads it every time it opens.
static REMEMBER: [AtomicUsize; PLAYERS] = [ZUS; PLAYERS];
// Set to true to log every tag assignment and every tag name shown outside a match (for debugging).
const DIAG: bool = false;
static TEXT_LOGS: AtomicU32 = AtomicU32::new(0);
static TS_LOGS: AtomicU32 = AtomicU32::new(0);
static PLATE_LOGS: AtomicU32 = AtomicU32::new(0);
static TAGSET_COUNT: AtomicU32 = AtomicU32::new(0); // how many times the game stored a tag number
static LAST_COUNT: AtomicU32 = AtomicU32::new(0); // that count at the previous match start
// (original name, new name, pointer to the new name as NUL-terminated UTF-16) for players whose tag we changed
static SUBST: Mutex<Vec<(String, String, usize)>> = Mutex::new(Vec::new());
// Only text whose buffer lives in the game's static data counts as a permanent name plate;
// the temporary match-intro panes use heap buffers and may be gone by the time we want them.
const STATIC_DATA_SPAN: usize = 0x6000000;
static CLOCK: OnceLock<Instant> = OnceLock::new();

fn now_ms() -> u64 {
    CLOCK.get_or_init(Instant::now).elapsed().as_millis() as u64
}

fn log(msg: &str) {
    if let Ok(mut f) = OpenOptions::new().create(true).append(true).open("sd:/tag_swap_log.txt") {
        let _ = writeln!(f, "[{} ms] {}", now_ms(), msg);
    }
}

fn plausible(p: usize) -> bool {
    p % 8 == 0 && p >= 0x10000 && p < 0x80_0000_0000
}

// ---- Finding things --------------------------------------------------------------------------
unsafe fn word_at(base: usize, off: usize) -> u32 {
    *((base + off) as *const u32)
}

unsafe fn find_pattern(base: usize) -> Option<usize> {
    let end = getRegionAddress(Region::Rodata) as usize;
    if end <= base {
        return None;
    }
    let code = std::slice::from_raw_parts(base as *const u8, end - base);
    for (i, w) in code.windows(PATTERN.len()).enumerate() {
        if w == PATTERN {
            return Some(i);
        }
    }
    None
}

unsafe fn decode_global(base: usize, adrp_off: usize) -> Option<usize> {
    let adrp = word_at(base, adrp_off);
    let ldr = word_at(base, adrp_off + 4);
    if adrp & 0x9F00_0000 != 0x9000_0000 || ldr & 0xFFC0_0000 != 0xF940_0000 {
        return None;
    }
    let immlo = ((adrp >> 29) & 0b11) as i64;
    let immhi = ((adrp >> 5) & 0x7FFFF) as i64;
    let imm21 = (immhi << 2) | immlo;
    let imm = ((imm21 << 43) >> 43) << 12;
    let page = (adrp_off as i64 & !0xFFF) + imm;
    let ldr_imm = (((ldr >> 10) & 0xFFF) as usize) << 3;
    Some(page as usize + ldr_imm)
}

// text base + TAG_GLOBAL -> one -> two -> (+0x58) -> a -> b -> first record
unsafe fn tag_table(base: usize, shift: i64) -> Option<usize> {
    let one = *((base as i64 + TAG_GLOBAL as i64 + shift) as usize as *const usize);
    if !plausible(one) {
        return None;
    }
    let two = *(one as *const usize);
    if !plausible(two) {
        return None;
    }
    let a = *((two + 0x58) as *const usize);
    if !plausible(a) {
        return None;
    }
    let b = *(a as *const usize);
    if !plausible(b) {
        return None;
    }
    let first = *(b as *const usize);
    if !plausible(first) {
        return None;
    }
    Some(first)
}

unsafe fn live_array(base: usize, shift: i64) -> Option<usize> {
    let blk = *((base as i64 + LIVE_GLOBAL as i64 + shift) as usize as *const usize);
    if !plausible(blk) {
        return None;
    }
    Some(blk + LIVE_ARRAY)
}


// The player slot that uses the controller with this id, from what character select taught us
// (None if we never saw that controller join).
unsafe fn controller_to_player(npad: usize, _base: usize, _shift: i64) -> Option<usize> {
    let table: Vec<u32> = (0..PLAYERS).map(|p| SLOT_CTRL[p].load(Ordering::Relaxed)).collect();
    let mut found = (0..PLAYERS).find(|&p| table[p] as usize == npad + 1 && SLOT_TAG[p].load(Ordering::Relaxed) != 0);
    let mut how = "learned at character select";
    if found.is_none() {
        // We never saw this controller join, so work it out from what is left over. Players that
        // are in the match and have no controller yet:
        let open: Vec<usize> = (0..PLAYERS)
            .filter(|&p| SLOT_TAG[p].load(Ordering::Relaxed) != 0 && table[p] == 0)
            .collect();
        if open.len() == 1 {
            found = Some(open[0]);
            how = "by elimination";
        } else if open.contains(&npad) {
            // port number = player number is the usual case, and nobody else owns that player
            found = Some(npad);
            how = "port number, nobody else owns that player";
        } else {
            // Other controllers that pressed buttons at character select but are still unknown most
            // likely own the player whose number matches their port. Rule those players out.
            let seen = SEEN_IDS.load(Ordering::Relaxed);
            let rest: Vec<usize> = open
                .iter()
                .copied()
                .filter(|&p| !(p < 64 && p != npad && seen & (1u64 << p) != 0 && !table.iter().any(|&t| t as usize == p + 1)))
                .collect();
            if rest.len() == 1 {
                found = Some(rest[0]);
                how = "left over after ruling out the other controllers";
            } else {
                how = "unknown";
            }
        }
    }
    log(&format!("controller {} pressed; controller per slot (id+1, 0 = unknown) {:?}; player slot {:?} ({})", npad, table, found, how));
    found
}


unsafe fn tag_name(rec: usize) -> Option<String> {
    let len = *((rec + TAG_NAME_LEN) as *const u32) as usize;
    if len == 0 || len > 10 {
        return None;
    }
    let s = std::slice::from_raw_parts((rec + TAG_NAME) as *const u16, len);
    Some(String::from_utf16_lossy(s))
}

// (is the game in result mode, how many fighters exist)
unsafe fn fm_state() -> (bool, i32) {
    let addr = FM_ADDR.load(Ordering::Relaxed);
    if addr == 0 {
        return (false, 0);
    }
    let mgr = *(addr as *mut *mut app::FighterManager);
    if mgr.is_null() {
        return (false, 0);
    }
    (FighterManager::is_result_mode(mgr), FighterManager::entry_count(mgr) as i32)
}

// ---- Watching the game's own functions -------------------------------------------------------
// Runs the game's tag-setting function unchanged, then notes which player slot got which tag.
unsafe extern "C" fn hook_tagset(a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize, a6: usize, a7: usize) -> usize {
    let o = ORIG_TAGSET.load(Ordering::Relaxed);
    let r = if o.is_null() {
        0
    } else {
        let f: unsafe extern "C" fn(usize, usize, usize, usize, usize, usize, usize, usize) -> usize = std::mem::transmute(o);
        f(a0, a1, a2, a3, a4, a5, a6, a7)
    };
    TAGSET_COUNT.fetch_add(1, Ordering::Relaxed);
    if plausible(a0) && plausible(a1 & !7) {
        let slot = *((a0 + 0x1d4) as *const u8) as usize;
        let tag = *(a1 as *const u8) as u32;
        let base = BASE.load(Ordering::Relaxed);
        if slot < PLAYERS && base != 0 && a1 >= base && a1 < base + STATIC_DATA_SPAN {
            REMEMBER[slot].store(a1, Ordering::Relaxed);
        }
        if DIAG && TS_LOGS.fetch_add(1, Ordering::Relaxed) < 200 {
            let nb = std::slice::from_raw_parts(a1 as *const u8, 8);
            log(&format!("TAGSET slot {} tag {} (byte at {:#x}, next bytes {:02x?}, object {:#x}, in_match {})", slot, tag, a1, &nb[1..], a0, IN_MATCH.load(Ordering::Relaxed)));
        }
        if slot < PLAYERS && !IN_MATCH.load(Ordering::Relaxed) {
            let lp = LAST_PRESS_ID.load(Ordering::Relaxed);
            let age = now_ms().saturating_sub(LAST_PRESS_MS.load(Ordering::Relaxed));
            if lp != 0 && age < 150 {
                let pm = LAST_PRESS_MS.load(Ordering::Relaxed);
                let mut stamp = true;
                if STAMP_PRESS_MS.load(Ordering::Relaxed) != pm {
                    STAMP_PRESS_MS.store(pm, Ordering::Relaxed);
                    STAMP_SLOT.store(slot, Ordering::Relaxed);
                    STAMP_BLOCKED.store(false, Ordering::Relaxed);
                } else if STAMP_BLOCKED.load(Ordering::Relaxed) {
                    stamp = false;
                } else if STAMP_SLOT.load(Ordering::Relaxed) != slot {
                    // a second slot from the same press: this is a burst, not a join
                    let first = STAMP_SLOT.load(Ordering::Relaxed);
                    if first < PLAYERS && SLOT_CTRL[first].load(Ordering::Relaxed) == lp {
                        SLOT_CTRL[first].store(0, Ordering::Relaxed);
                    }
                    STAMP_BLOCKED.store(true, Ordering::Relaxed);
                    stamp = false;
                }
                if stamp {
                for q in 0..PLAYERS {
                    if q != slot && SLOT_CTRL[q].load(Ordering::Relaxed) == lp {
                        SLOT_CTRL[q].store(0, Ordering::Relaxed); // one controller, one player
                    }
                }
                SLOT_CTRL[slot].store(lp, Ordering::Relaxed);
                log(&format!("slot {} is used by controller {} (pressed {} ms before its tag was set)", slot, lp - 1, age));
                }
            }
        }
        if slot < PLAYERS && tag as usize <= MAX_TAG {
            SLOT_TAG[slot].store(tag, Ordering::Relaxed);
            TAGPTR[slot].store(a1, Ordering::Relaxed);
        }
    }
    r
}

// Runs the game's text-setting function. During a match it remembers which panes were given a
// player's name (the permanent plates), and after a tag change it swaps the old name for the new one
// in any name text the game sets (for example on the results screen).
unsafe extern "C" fn hook_text(a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize, a6: usize, a7: usize) -> usize {
    let mut a1 = a1;
    let mut a2 = a2;
    let in_match = IN_MATCH.load(Ordering::Relaxed);
    let subst = SUBST_ACTIVE.load(Ordering::Relaxed);
    if (in_match || subst || (DIAG && TEXT_LOGS.load(Ordering::Relaxed) < 400)) && a1 % 2 == 0 && plausible(a1 & !7) {
        let n = a2 as u32;
        let tp = a1 as *const u16;
        let mut len = 0usize;
        if n == 0xffff_ffff {
            while len < 11 && *tp.add(len) != 0 {
                len += 1;
            }
        } else if n >= 1 && n <= 10 {
            len = n as usize;
        }
        if len >= 1 && len <= 10 {
            let mut txt = String::from_utf16_lossy(std::slice::from_raw_parts(tp, len));
            if DIAG && !in_match && TEXT_LOGS.load(Ordering::Relaxed) < 400 {
                let known = match NAMES.try_lock() {
                    Ok(g) => g.iter().any(|x| *x == txt),
                    Err(_) => false,
                };
                if known {
                    TEXT_LOGS.fetch_add(1, Ordering::Relaxed);
                    log(&format!("TEXT outside match: pane {:#x} text pointer {:#x} length arg {:#x} text {:?}", a0, a1, a2, txt));
                }
            }
            // outside a match only length-based name text (the results screen) is swapped; the character
            // select tag list uses NUL-terminated text and must show the real names
            if subst && (in_match || n != 0xffff_ffff) {
                if let Ok(g) = SUBST.try_lock() {
                    if let Some(x) = g.iter().find(|x| x.0 == txt) {
                        a1 = x.2;
                        a2 = 0xffff_ffff;
                        txt = x.1.clone();
                    }
                }
            }
            if in_match && n == 0xffff_ffff && plausible(a0) {
                // NUL-terminated name text = a name plate (the character-name panes use a length instead)
                let known = match NAMES.try_lock() {
                    Ok(g) => g.iter().any(|x| *x == txt),
                    Err(_) => false,
                };
                if known {
                    let vt = *(a0 as *const usize);
                    let owner = match PNAME.try_lock() {
                        Ok(g) => g.iter().position(|x| *x == txt).unwrap_or(usize::MAX),
                        Err(_) => usize::MAX,
                    };
                    if DIAG && PLATE_LOGS.fetch_add(1, Ordering::Relaxed) < 200 {
                        log(&format!("plate registered: pane {:#x} name {:?} belongs to player slot {}", a0, txt, if owner == usize::MAX { -1 } else { owner as i64 }));
                    }
                    if let Ok(mut g) = PANES.try_lock() {
                        g.retain(|x| x.0 != a0);
                        g.push((a0, a3, txt, vt, owner));
                        if g.len() > 256 {
                            g.remove(0);
                        }
                    }
                }
            }
        }
    }
    let o = ORIG_TEXT.load(Ordering::Relaxed);
    if o.is_null() {
        return 0;
    }
    let f: unsafe extern "C" fn(usize, usize, usize, usize, usize, usize, usize, usize) -> usize = std::mem::transmute(o);
    f(a0, a1, a2, a3, a4, a5, a6, a7)
}

// ---- Controller hook -------------------------------------------------------------------------
unsafe fn on_state(_kind: usize, state: *mut NpadHandheldState, id: *const u32, slot_index: usize) {
    let _ = id;
    let raw = (*state).Buttons;
    let prev = PREV[slot_index].swap(raw, Ordering::Relaxed);
    if !IN_MATCH.load(Ordering::Relaxed) {
        if raw & !prev != 0 {
            SEEN_IDS.fetch_or(1u64 << (slot_index % 64), Ordering::Relaxed);
            LAST_PRESS_ID.store((slot_index % 64) as u32 + 1, Ordering::Relaxed);
            LAST_PRESS_MS.store(now_ms(), Ordering::Relaxed);
        }
        return;
    }
    if (raw & SHOULDER_MASK).count_ones() < 2 {
        return;
    }
    // The controller's id. The loop thread turns it into a player slot with the game's own table
    // (players are numbered in join order at character select, not by controller port).
    let player = slot_index % 64;
    let pressed = raw & !prev;
    let dir = if pressed & NEXT_KEYS != 0 {
        1
    } else if pressed & PREV_KEYS != 0 {
        2
    } else {
        0
    };
    if dir != 0 {
        let now = now_ms();
        if now.saturating_sub(LAST_CMD_MS.load(Ordering::Relaxed)) > 150 {
            LAST_CMD_MS.store(now, Ordering::Relaxed);
            CMD.store(((_kind as u32) << 16) | ((player as u32) << 8) | dir, Ordering::Relaxed);
        }
    }
    // The direction buttons belong to us while the shoulders are held (no taunts by accident).
    (*state).Buttons &= !(KEY_LEFT | KEY_RIGHT | KEY_X | KEY_Y);
}

macro_rules! make_hook {
    ($name:ident, $kind:expr, $ty:ty) => {
        unsafe extern "C" fn $name(state: *mut $ty, id: *const u32) {
            let orig = ORIG[$kind].load(Ordering::Relaxed);
            if !orig.is_null() {
                let f: unsafe extern "C" fn(*mut $ty, *const u32) = std::mem::transmute(orig);
                f(state, id);
            }
            let idn = if id.is_null() { 0 } else { (*id & 63) as usize };
            on_state($kind, state as *mut NpadHandheldState, id, $kind * 64 + idn);
        }
    };
}
make_hook!(hook_fullkey, 0, NpadHandheldState);
make_hook!(hook_handheld, 1, NpadHandheldState);
make_hook!(hook_joydual, 2, NpadHandheldState);
make_hook!(hook_joyleft, 3, NpadHandheldState);
make_hook!(hook_joyright, 4, NpadHandheldState);
make_hook!(hook_gc, 5, NpadGcState);

fn install_input_hooks() {
    let hooks: [usize; 6] = [
        hook_fullkey as usize,
        hook_handheld as usize,
        hook_joydual as usize,
        hook_joyleft as usize,
        hook_joyright as usize,
        hook_gc as usize,
    ];
    for i in 0..6 {
        let mut addr: usize = 0;
        unsafe {
            LookupSymbol(&mut addr, SYMBOLS[i].as_ptr());
        }
        if addr == 0 {
            log(&format!("symbol NOT found for {}", KIND_NAMES[i]));
            continue;
        }
        unsafe {
            A64HookFunction(addr as *const c_void, hooks[i] as *const c_void, ORIG[i].as_ptr());
        }
        log(&format!("hooked {}", KIND_NAMES[i]));
    }
}

// ---- The actual change -----------------------------------------------------------------------
fn refresh_names(base: usize, shift: i64) {
    if let Some(t) = unsafe { tag_table(base, shift) } {
        let list: Vec<String> = (1..=MAX_TAG).filter_map(|i| unsafe { tag_name(t + i * TAG_SIZE) }).collect();
        if let Ok(mut g) = NAMES.lock() {
            *g = list;
        }
    }
}

fn change_player(player: usize, dir: u32, base: usize, shift: i64) {
    let t = match unsafe { tag_table(base, shift) } {
        Some(t) => t,
        None => {
            log("tag table not available; nothing changed");
            return;
        }
    };
    let l = match unsafe { live_array(base, shift) } {
        Some(l) => l,
        None => {
            log("live settings not available; nothing changed");
            return;
        }
    };
    if player >= PLAYERS {
        return;
    }
    let cur = CUR_TAG[player].load(Ordering::Relaxed) as usize;
    // like the game, don't hand out a tag another player is already using
    let used_by_others: Vec<usize> = (0..PLAYERS)
        .filter(|&p| p != player)
        .map(|p| CUR_TAG[p].load(Ordering::Relaxed) as usize)
        .filter(|&c| c >= 1)
        .collect();
    let valid: Vec<usize> = (1..=MAX_TAG)
        .filter(|&i| !used_by_others.contains(&i) && unsafe { tag_name(t + i * TAG_SIZE) }.is_some())
        .collect();
    if valid.is_empty() {
        return;
    }
    let n = valid.len();
    let new_tag = match valid.iter().position(|&x| x == cur) {
        Some(i) => {
            if dir == 1 {
                valid[(i + 1) % n]
            } else {
                valid[(i + n - 1) % n]
            }
        }
        None => {
            if dir == 1 {
                valid[0]
            } else {
                valid[n - 1]
            }
        }
    };
    let rec = t + new_tag * TAG_SIZE;
    let new_name = unsafe { tag_name(rec) }.unwrap_or_default();
    let old_name = if cur >= 1 { unsafe { tag_name(t + cur * TAG_SIZE) } } else { None };

    // 1) the controller settings
    unsafe {
        std::ptr::copy_nonoverlapping((rec + TAG_MAP) as *const u8, (l + player * MAP_SIZE) as *mut u8, MAP_COPY);
    }
    CUR_TAG[player].store(new_tag as u32, Ordering::Relaxed);

    // 1b) the place the game read this player's tag number from (so character select and the next
    //     match see the new tag). Only written if it still holds the tag we expect.
    let tp = TAGPTR[player].load(Ordering::Relaxed);
    if tp != 0 && plausible(tp) {
        let v = unsafe { *(tp as *const u8) } as usize;
        if v == cur {
            unsafe { *(tp as *mut u8) = new_tag as u8 };
            log(&format!("tag source {:#x} updated: {} -> {}", tp, cur, new_tag));
        } else {
            log(&format!("tag source {:#x} holds {} not {}; left alone", tp, v, cur));
        }
    } else {
        log("no tag source known for this player; left alone");
    }

    // 1c) the game's remembered "last tag picked" for this player, so character select and the next
    //     loading screen show the new tag
    let rp = REMEMBER[player].load(Ordering::Relaxed);
    if rp != 0 && plausible(rp & !7) {
        let v = unsafe { *(rp as *const u8) } as usize;
        let off = rp.wrapping_sub(base);
        if v == cur {
            unsafe { *(rp as *mut u8) = new_tag as u8 };
            log(&format!("remembered tag at {:#x} (data offset {:#x}) updated: {} -> {}", rp, off, cur, new_tag));
        } else {
            log(&format!("remembered tag at {:#x} (data offset {:#x}) holds {} not {}; left alone", rp, off, v, cur));
        }
    } else {
        log("remembered tag spot not known for this player; left alone");
    }

    // 2) the name plates
    let mut renamed = 0;
    if let Some(old) = &old_name {
        let len = unsafe { *((rec + TAG_NAME_LEN) as *const u32) } as usize;
        let mut buf: Vec<u16> = unsafe { std::slice::from_raw_parts((rec + TAG_NAME) as *const u16, len) }.to_vec();
        buf.push(0);
        let ptr = Box::leak(buf.into_boxed_slice()).as_ptr() as usize;
        let targets: Vec<(usize, usize, usize)> = match PANES.lock() {
            Ok(g) => g.iter().filter(|x| x.4 == player).map(|x| (x.0, x.1, x.3)).collect(),
            Err(_) => Vec::new(),
        };
        let o = ORIG_TEXT.load(Ordering::Relaxed);
        if !o.is_null() {
            let f: unsafe extern "C" fn(usize, usize, usize, usize, usize, usize, usize, usize) -> usize = unsafe { std::mem::transmute(o) };
            let mut stale = Vec::new();
            for (pane, a3, vt) in &targets {
                // Only touch a pane that still looks exactly like when we saw the game fill it.
                let ok = plausible(*pane) && *vt != 0 && unsafe { *(*pane as *const usize) } == *vt;
                if !ok {
                    log(&format!("skipping pane {:#x}: it has changed or gone", pane));
                    stale.push(*pane);
                    continue;
                }
                log(&format!("rewriting pane {:#x}", pane));
                unsafe {
                    f(*pane, ptr, 0xffff_ffff, *a3, 0, 0, 0, 0);
                }
                renamed += 1;
            }
            if !stale.is_empty() {
                if let Ok(mut g) = PANES.lock() {
                    g.retain(|x| !stale.contains(&x.0));
                }
            }
        }
        if let Ok(mut g) = PANES.lock() {
            for x in g.iter_mut() {
                if x.4 == player {
                    x.2 = new_name.clone();
                }
            }
        }
    }
    if let Ok(mut g) = PNAME.lock() {
        if g.len() < PLAYERS {
            g.resize(PLAYERS, String::new());
        }
        g[player] = new_name.clone();
    }
    // 3) later name text (results screen and so on): swap the original name for the current one
    {
        let mut pairs: Vec<(String, String, usize)> = Vec::new();
        for p in 0..PLAYERS {
            let o = ORIG_TAG[p].load(Ordering::Relaxed) as usize;
            let c = CUR_TAG[p].load(Ordering::Relaxed) as usize;
            if o >= 1 && c >= 1 && o != c {
                let (orec, crec) = (t + o * TAG_SIZE, t + c * TAG_SIZE);
                if let (Some(on), Some(cn)) = (unsafe { tag_name(orec) }, unsafe { tag_name(crec) }) {
                    let len = unsafe { *((crec + TAG_NAME_LEN) as *const u32) } as usize;
                    let mut buf: Vec<u16> = unsafe { std::slice::from_raw_parts((crec + TAG_NAME) as *const u16, len) }.to_vec();
                    buf.push(0);
                    let ptr = Box::leak(buf.into_boxed_slice()).as_ptr() as usize;
                    pairs.push((on, cn, ptr));
                }
            }
        }
        if let Ok(mut g) = SUBST.lock() {
            *g = pairs;
        }
        SUBST_ACTIVE.store(true, Ordering::Relaxed);
    }
    log(&format!(
        "player {} : tag {} ({:?}) -> tag {} ({:?}); controller settings copied; {} name text panes rewritten",
        player + 1,
        cur,
        old_name,
        new_tag,
        new_name,
        renamed
    ));
}

#[skyline::main(name = "tag_swap")]
pub fn main() {
    let _ = now_ms();
    log("tag_swap loaded");
    std::thread::spawn(|| {
        std::thread::sleep(Duration::from_secs(20));
        let base = unsafe { getRegionAddress(Region::Text) as usize };
        BASE.store(base, Ordering::Relaxed);

        // Work out the shift between HewDraw Remix's data addresses and this game's, and only go on
        // if it is the one known for game version 13.0.4.
        let shift = match unsafe { find_pattern(base) } {
            Some(pos) => match unsafe { decode_global(base, pos + ADRP_AFTER_PATTERN) } {
                Some(g) => g as i64 - HDR_GAME_STATE_GLOBAL,
                None => {
                    log("could not decode the game-state global; staying idle");
                    return;
                }
            },
            None => {
                log("byte pattern not found; staying idle (the game version may differ)");
                return;
            }
        };
        if shift != EXPECTED_SHIFT {
            log(&format!("data shift is {} not the expected {}; staying idle (the game version may differ)", shift, EXPECTED_SHIFT));
            return;
        }

        let mut fm: usize = 0;
        unsafe {
            LookupSymbol(&mut fm, "_ZN3lib9SingletonIN3app14FighterManagerEE9instance_E\0".as_ptr());
        }
        FM_ADDR.store(fm, Ordering::Relaxed);

        unsafe {
            A64HookFunction((base + (TAGSET_FN - GHIDRA_BASE)) as *const c_void, hook_tagset as *const c_void, ORIG_TAGSET.as_ptr());
            A64HookFunction((base + (TEXTSET_FN - GHIDRA_BASE)) as *const c_void, hook_text as *const c_void, ORIG_TEXT.as_ptr());
        }
        install_input_hooks();
        log("ready: hold two shoulder buttons + D-pad Right/X (next tag) or D-pad Left/Y (previous tag) during a match");

        let mut was_in_match = false;
        let mut last_names = Instant::now();
        loop {
            let (results, count) = unsafe { fm_state() };
            let in_match = !results && count > 0;
            if in_match && !was_in_match {
                refresh_names(base, shift);
                if let Ok(mut g) = PANES.lock() {
                    g.clear();
                }
                // A match started from character select stores the tags again; a restart straight from
                // the results screen does not. Only in the second case do our earlier changes carry on.
                let cnt = TAGSET_COUNT.load(Ordering::Relaxed);
                let fresh = cnt != LAST_COUNT.swap(cnt, Ordering::Relaxed);
                if fresh {
                    SUBST_ACTIVE.store(false, Ordering::Relaxed);
                    if let Ok(mut g) = SUBST.lock() {
                        g.clear();
                    }
                }
                if !SUBST_ACTIVE.load(Ordering::Relaxed) {
                    for p in 0..PLAYERS {
                        let v = SLOT_TAG[p].load(Ordering::Relaxed);
                        CUR_TAG[p].store(v, Ordering::Relaxed);
                        ORIG_TAG[p].store(v, Ordering::Relaxed);
                    }
                } else if let (Some(t), Some(l)) = (unsafe { tag_table(base, shift) }, unsafe { live_array(base, shift) }) {
                    // a restart without going back to character select: the game reset the live
                    // settings to the original tags, so put our changes back
                    for p in 0..PLAYERS {
                        let c = CUR_TAG[p].load(Ordering::Relaxed) as usize;
                        if c >= 1 && c != ORIG_TAG[p].load(Ordering::Relaxed) as usize {
                            unsafe { std::ptr::copy_nonoverlapping((t + c * TAG_SIZE + TAG_MAP) as *const u8, (l + p * MAP_SIZE) as *mut u8, MAP_COPY) };
                        }
                    }
                }
                for p in 0..PLAYERS {
                    let tp = TAGPTR[p].load(Ordering::Relaxed);
                    if p == 0 || SLOT_TAG[p].load(Ordering::Relaxed) != 0 {
                        let v = if tp != 0 && plausible(tp) { (unsafe { *(tp as *const u8) }) as i64 } else { -1 };
                        log(&format!("slot {}: tag {} ; tag source {:#x} currently holds {}", p, SLOT_TAG[p].load(Ordering::Relaxed), tp, v));
                    }
                }
                if let Some(t) = unsafe { tag_table(base, shift) } {
                    let names: Vec<String> = (0..PLAYERS)
                        .map(|p| {
                            let c = CUR_TAG[p].load(Ordering::Relaxed) as usize;
                            if c >= 1 && c <= MAX_TAG { unsafe { tag_name(t + c * TAG_SIZE) }.unwrap_or_default() } else { String::new() }
                        })
                        .collect();
                    if let Ok(mut g) = PNAME.lock() {
                        *g = names;
                    }
                }
                IN_MATCH.store(true, Ordering::Relaxed);
                log(&format!(
                    "match began; tags per player slot: {:?}",
                    (0..PLAYERS).map(|p| CUR_TAG[p].load(Ordering::Relaxed)).collect::<Vec<_>>()
                ));
            } else if !in_match && was_in_match {
                IN_MATCH.store(false, Ordering::Relaxed);
                SEEN_IDS.store(0, Ordering::Relaxed);
                if let Ok(mut g) = PANES.lock() {
                    g.clear();
                }
                CMD.store(0, Ordering::Relaxed);
                log("match ended");
            }
            was_in_match = in_match;
            SUBST_TEXT.store(SUBST_ACTIVE.load(Ordering::Relaxed) && (results || in_match), Ordering::Relaxed);
            if SUBST_ACTIVE.load(Ordering::Relaxed) && !results && count == 0 && !in_match {
                SUBST_ACTIVE.store(false, Ordering::Relaxed);
                if let Ok(mut g) = SUBST.lock() {
                    g.clear();
                }
                log("back out of the match/results: name substitution cleared");
            }

            if !in_match && last_names.elapsed() > Duration::from_secs(3) {
                refresh_names(base, shift);
                last_names = Instant::now();
            }

            let cmd = CMD.swap(0, Ordering::Relaxed);
            if cmd != 0 && in_match {
                let npad = ((cmd >> 8) & 0xff) as usize;
                // fall back to "port = player" (handheld counts as player 1) if the table fails
                let player = unsafe { controller_to_player(npad, base, shift) }.unwrap_or(if npad < PLAYERS { npad } else { 0 });
                change_player(player, cmd & 0xff, base, shift);
            }
            std::thread::sleep(Duration::from_millis(15));
        }
    });
}
