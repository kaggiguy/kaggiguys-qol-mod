#![feature(proc_macro_hygiene)]

// results_control_v2
//
// On the offline results screen:
//   Start alone                              -> leaves the results screen straight to stage select
//   L/ZL + R/ZR + A + Start                  -> REMATCH: straight back into a new match on the same stage
//                                               with the same fighters. No stage select, no character select.
//   L/ZL + R/ZR + A + B + Start (secret)     -> the old restart: restarts into the hidden results stage
//                                               (the Joker-effect version from results_control v1).
// Works from any controller. Remove results_control (v1), "skip results" and quick_rematch while this
// one is installed.
//
// How the rematch works: every time the game asks for its "ingame call" scene (the step right after
// character select that starts a match), this plugin saves a copy of that request. When you do the
// rematch combo it runs the game's own "leave results" call, and when the game then asks for its next
// scene (unlock / stage select) the plugin swaps that request for the saved match request. The game
// builds the match itself from the stage and fighters it already remembers.
//
// Safety: it finds the game's "game state" object the same way HewDraw Remix does, checks that the
// object's function table is the expected one for game version 13.0.4 and that the entry it wants is
// the expected function, and only then calls it. If anything does not match, it does nothing.
//
// Tuning (optional): sd:/results_control_v2.txt, lines like  min_results_ms=3500
// Log: sd:/results_control_v2_log.txt

use skyline::hooks::{getRegionAddress, Region};
use skyline::nn::hid::{NpadGcState, NpadHandheldState};
use skyline::nn::ro::LookupSymbol;
use smash::app::{self, lua_bind::*};
use std::ffi::c_void;
use std::fs::OpenOptions;
use std::io::Write;
use std::sync::atomic::{AtomicPtr, AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

// ---- Buttons ---------------------------------------------------------------------------------
const KEY_A: u64 = 1 << 0;
const KEY_B: u64 = 1 << 1;
const KEY_L: u64 = 1 << 6;
const KEY_R: u64 = 1 << 7;
const KEY_ZL: u64 = 1 << 8;
const KEY_ZR: u64 = 1 << 9;
const KEY_PLUS: u64 = 1 << 10;

fn lr_held(b: u64) -> bool {
    b & (KEY_L | KEY_ZL) != 0 && b & (KEY_R | KEY_ZR) != 0
}
fn combo_held(b: u64) -> bool {
    lr_held(b) && b & KEY_A != 0 && b & KEY_PLUS != 0
}

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

// ---- The game's state object (found like HewDraw Remix does) ---------------------------------
const PATTERN: [u8; 32] = [
    0xf5, 0x0f, 0x1d, 0xf8, 0xf4, 0x4f, 0x01, 0xa9, 0xfd, 0x7b, 0x02, 0xa9, 0xfd, 0x83, 0x00, 0x91,
    0x08, 0x14, 0x40, 0xb9, 0xf4, 0x03, 0x01, 0xaa, 0xf3, 0x03, 0x00, 0xaa, 0x1f, 0x05, 0x00, 0x71,
];
const ADRP_AFTER_PATTERN: usize = 0x28;
const GHIDRA_BASE: usize = 0x7100000000;
// Game version 13.0.4 (Ghidra addresses): the table of functions and the two entries we call.
const TABLE_GHIDRA: usize = 0x710506b088;
const EXIT_INDEX: usize = 3; // go to stage select
const EXIT_GHIDRA: usize = 0x71014d70e0;
const RESTART_INDEX: usize = 5; // restart the match
const RESTART_GHIDRA: usize = 0x71014d7770;

const ACT_NONE: u32 = 0;
const ACT_RESTART: u32 = 1;
const ACT_EXIT: u32 = 2;
const ACT_REMATCH: u32 = 3;

// Extra diagnostic logging (scene requests, saved-value diffs, fighter-id watcher). Off for normal use.
const DIAG: bool = false;

// The game's "ask for the next scene" function (game version 13.0.4, Ghidra address).
const ENQ_GHIDRA: usize = 0x7103726120;

// ---- Shared state ----------------------------------------------------------------------------
const NULLPTR: AtomicPtr<c_void> = AtomicPtr::new(std::ptr::null_mut());
static ORIG: [AtomicPtr<c_void>; 6] = [NULLPTR; 6];
const Z64: AtomicU64 = AtomicU64::new(0);
static PREV: [AtomicU64; 384] = [Z64; 384];
static PEND: [AtomicU64; 384] = [Z64; 384]; // per controller: when Start went down (+1), 0 = none
static FM_ADDR: AtomicUsize = AtomicUsize::new(0);
static ACTION: AtomicU32 = AtomicU32::new(ACT_NONE);
static RESULTS_SINCE: AtomicU64 = AtomicU64::new(0); // when the results screen began (+1), 0 = not in results
static HIDE_UNTIL: AtomicU64 = AtomicU64::new(0);
// How long into the results screen before any combo (rematch, restart, exit) is accepted. Calling the
// game's leave/restart too early crashes it: 1730 ms crashed, and every call at 3900 ms or later worked (3500 is being tried).
static MIN_RESULTS_MS: AtomicU64 = AtomicU64::new(3500);
static START_HOLD_MS: AtomicU64 = AtomicU64::new(100);
static HIDE_MS: AtomicU64 = AtomicU64::new(1000);
static ENABLE_RESTART: AtomicU64 = AtomicU64::new(1);
static ENABLE_EXIT: AtomicU64 = AtomicU64::new(1);
static ENABLE_REMATCH: AtomicU64 = AtomicU64::new(1);
static SECRET_WAIT_MS: AtomicU64 = AtomicU64::new(120);
static SWAP_AT_UNLOCK: AtomicU64 = AtomicU64::new(1); // 1 = also swap the "unlock" request
static RESTORE_IDS: AtomicU64 = AtomicU64::new(1); // 1 = put the fighter ids back before the rematch starts
static COMBO_PEND: AtomicU64 = AtomicU64::new(0); // when the combo went down (+1), 0 = none
static COMBO_SECRET: AtomicU64 = AtomicU64::new(0); // B was seen while the combo was pending
static ORIG_ENQ: AtomicPtr<c_void> = AtomicPtr::new(std::ptr::null_mut());
static BASE_ADDR: AtomicUsize = AtomicUsize::new(0);
static ARMED_UNTIL: AtomicU64 = AtomicU64::new(0); // rematch armed until this time (+1), 0 = not armed

// Saved copy of the stack area that held the game's last "ingame call" scene request.
const SNAP_LEN: usize = 0x500;
#[repr(C, align(16))]
struct Snap([u8; SNAP_LEN]);
static mut SNAP: Snap = Snap([0; SNAP_LEN]);
static SNAP_OK: AtomicU64 = AtomicU64::new(0);
static SNAP_OFF1: AtomicUsize = AtomicUsize::new(0);
static SNAP_OFF2: AtomicUsize = AtomicUsize::new(0);
static SNAP_OFF3: AtomicUsize = AtomicUsize::new(0);
static CLOCK: OnceLock<Instant> = OnceLock::new();

fn now_ms() -> u64 {
    CLOCK.get_or_init(Instant::now).elapsed().as_millis() as u64
}

fn log(msg: &str) {
    if let Ok(mut f) = OpenOptions::new().create(true).append(true).open("sd:/results_control_v2_log.txt") {
        let _ = writeln!(f, "[{} ms] {}", now_ms(), msg);
    }
}

fn gh(addr: usize, base: usize) -> String {
    if addr >= base && addr < base + 0x8000000 {
        format!("ghidra 0x{:x}", addr - base + GHIDRA_BASE)
    } else {
        format!("raw 0x{:x}", addr)
    }
}

fn plausible(p: usize) -> bool {
    p % 8 == 0 && p >= 0x10000 && p < 0x80_0000_0000
}

unsafe fn word_at(base: usize, off: usize) -> u32 {
    *((base + off) as *const u32)
}

unsafe fn find_pattern(base: usize) -> Option<(usize, usize)> {
    let end = getRegionAddress(Region::Rodata) as usize;
    if end <= base {
        return None;
    }
    let code = std::slice::from_raw_parts(base as *const u8, end - base);
    let mut first = None;
    let mut count = 0;
    for (i, w) in code.windows(PATTERN.len()).enumerate() {
        if w == PATTERN {
            if first.is_none() {
                first = Some(i);
            }
            count += 1;
        }
    }
    first.map(|f| (f, count))
}

// Decodes "adrp xN, page" + "ldr xM, [xN, #imm]" into the offset (from the text base) of the global.
unsafe fn decode_global(base: usize, adrp_off: usize) -> Option<usize> {
    let adrp = word_at(base, adrp_off);
    let ldr = word_at(base, adrp_off + 4);
    if adrp & 0x9F00_0000 != 0x9000_0000 || ldr & 0xFFC0_0000 != 0xF940_0000 {
        log(&format!("unexpected instructions at the pattern: {:#010x} {:#010x}", adrp, ldr));
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

unsafe fn in_results() -> bool {
    let (r, e) = fm_state();
    r && e > 0
}


// ---- Diagnostics: which of the game's saved selection values does a match change? ----------------
const REGIONS: [(usize, usize); 3] = [(0x7105307798, 0xE40), (0x71053097a0, 0xA0), (0x71052c45d0, 0x160)];
const REG_TOTAL: usize = 0xE40 + 0xA0 + 0x160;
static mut REG_SNAP: [u8; REG_TOTAL] = [0; REG_TOTAL];
static REG_OK: AtomicU64 = AtomicU64::new(0);

unsafe fn take_region_snapshot() {
    let base = BASE_ADDR.load(Ordering::Relaxed);
    if base == 0 {
        return;
    }
    let dst = std::ptr::addr_of_mut!(REG_SNAP) as *mut u8;
    let mut off = 0usize;
    for (g, len) in REGIONS.iter() {
        std::ptr::copy_nonoverlapping((base + (g - GHIDRA_BASE)) as *const u8, dst.add(off), *len);
        off += *len;
    }
    REG_OK.store(1, Ordering::Relaxed);
}

unsafe fn log_region_diff(label: &str) {
    if !DIAG || REG_OK.load(Ordering::Relaxed) != 1 {
        return;
    }
    let base = BASE_ADDR.load(Ordering::Relaxed);
    let snap = std::ptr::addr_of!(REG_SNAP) as *const u8;
    let mut off = 0usize;
    let mut total = 0usize;
    let mut lines = Vec::new();
    for (ri, (g, len)) in REGIONS.iter().enumerate() {
        let cur = (base + (g - GHIDRA_BASE)) as *const u8;
        let mut i = 0usize;
        while i + 8 <= *len {
            let old = *(snap.add(off + i) as *const u64);
            let new = *(cur.add(i) as *const u64);
            if old != new {
                total += 1;
                if lines.len() < 60 {
                    lines.push(format!("R{}+{:#x}: {:x} -> {:x}", ri, i, old, new));
                }
            }
            i += 8;
        }
        off += *len;
    }
    log(&format!("DIFF vs match start ({}): {} changed words", label, total));
    for l in lines {
        log(&format!("    {}", l));
    }
}


// The player entries (8 of them, 0x1c8 bytes each, at the start of the first region) hold the chosen
// fighter's id in two words (+0x10 and +0x18). The game wipes them on its way back to character select;
// before a rematch we put the saved values back, so the fighters load again.
const ENTRY_STRIDE: usize = 0x1c8;

unsafe fn restore_ids() {
    if RESTORE_IDS.load(Ordering::Relaxed) == 0 || REG_OK.load(Ordering::Relaxed) != 1 {
        return;
    }
    let base = BASE_ADDR.load(Ordering::Relaxed);
    let snap = std::ptr::addr_of!(REG_SNAP) as *const u8;
    let live = (base + (REGIONS[0].0 - GHIDRA_BASE)) as *mut u8;
    let mut fixed = 0;
    for i in 0..8usize {
        for off in [0x10usize, 0x18usize] {
            let o = i * ENTRY_STRIDE + off;
            let old = *(snap.add(o) as *const u64);
            let cur = *(live.add(o) as *const u64);
            if old != cur {
                *(live.add(o) as *mut u64) = old;
                fixed += 1;
                log(&format!("REMATCH: restored entry {} +{:#x}: {:x} -> {:x}", i, off, cur, old));
            }
        }
    }
    log(&format!("REMATCH: restored {} fighter id words", fixed));
}

static WATCH_LAST: [AtomicU64; 4] = [Z64; 4];
unsafe fn watch_ids() {
    if !DIAG {
        return;
    }
    let base = BASE_ADDR.load(Ordering::Relaxed);
    if base == 0 {
        return;
    }
    let live = (base + (REGIONS[0].0 - GHIDRA_BASE)) as *const u8;
    let vals = [
        *(live.add(0x10) as *const u64),
        *(live.add(0x18) as *const u64),
        *(live.add(ENTRY_STRIDE + 0x10) as *const u64),
        *(live.add(ENTRY_STRIDE + 0x18) as *const u64),
    ];
    let mut changed = false;
    for i in 0..4 {
        if WATCH_LAST[i].swap(vals[i], Ordering::Relaxed) != vals[i] {
            changed = true;
        }
    }
    if changed {
        log(&format!("WATCH fighter ids: p1 {:x} {:x} | p2 {:x} {:x}", vals[0], vals[1], vals[2], vals[3]));
    }
}

// ---- Scene request hook ----------------------------------------------------------------------
unsafe fn peek_name(p: usize) -> String {
    if p < 0x1000_0000 || p >= 0x100_0000_0000 || p % 4 != 0 {
        return String::new();
    }
    let mut out = String::new();
    for i in 0..64usize {
        let b = *((p + 8 + i) as *const u8);
        if b == 0 {
            break;
        }
        if b < 0x20 || b > 0x7e {
            out.push('?');
        } else {
            out.push(b as char);
        }
    }
    out
}

// Copies the stack area around the request (the two name blocks and the small "factory" object that
// builds the scene's parameters) into our own buffer, fixing up pointers that point inside that area.
unsafe fn capture_snapshot(a1: usize, a2: usize, a3: usize) {
    let lo = a1.min(a2).min(a3);
    let hi = a1.max(a2).max(a3);
    if hi - lo > 0x300 || lo % 8 != 0 {
        log(&format!("saving the match request: blocks too far apart ({:#x} {:#x} {:#x}); not saved", a1, a2, a3));
        return;
    }
    let dst = std::ptr::addr_of_mut!(SNAP) as *mut u8;
    std::ptr::copy_nonoverlapping(lo as *const u8, dst, SNAP_LEN);
    let delta = (dst as usize).wrapping_sub(lo);
    let words = dst as *mut usize;
    for i in 0..SNAP_LEN / 8 {
        let w = *words.add(i);
        if w >= lo && w < lo + SNAP_LEN {
            *words.add(i) = w.wrapping_add(delta);
        }
    }
    SNAP_OFF1.store(a1 - lo, Ordering::Relaxed);
    SNAP_OFF2.store(a2 - lo, Ordering::Relaxed);
    SNAP_OFF3.store(a3 - lo, Ordering::Relaxed);
    SNAP_OK.store(1, Ordering::Relaxed);
}

unsafe extern "C" fn hook_enq(a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize, a6: usize, a7: usize) -> usize {
    let orig = ORIG_ENQ.load(Ordering::Relaxed);
    if orig.is_null() {
        return 0;
    }
    let f: unsafe extern "C" fn(usize, usize, usize, usize, usize, usize, usize, usize) -> usize = std::mem::transmute(orig);
    let name_a = peek_name(a1);
    let now = now_ms();
    let armed = ARMED_UNTIL.load(Ordering::Relaxed);
    if DIAG {
        log(&format!("scene request: '{}'{}", name_a, if armed != 0 { " (rematch armed)" } else { "" }));
    }

    // Rematch: swap the request for the next scene (after the match) for the saved match request.
    if armed != 0 && now + 1 <= armed
        && ((name_a == "UnlockSequenceScene" && SWAP_AT_UNLOCK.load(Ordering::Relaxed) != 0)
            || name_a == "StageSelectScene"
            || name_a == "CharaSelectScene")
        && SNAP_OK.load(Ordering::Relaxed) == 1
    {
        ARMED_UNTIL.store(0, Ordering::Relaxed);
        let b = std::ptr::addr_of_mut!(SNAP) as usize;
        let s1 = b + SNAP_OFF1.load(Ordering::Relaxed);
        let s2 = b + SNAP_OFF2.load(Ordering::Relaxed);
        let s3 = b + SNAP_OFF3.load(Ordering::Relaxed);
        log(&format!("REMATCH: the game asked for '{}'; asking for '{}' instead", name_a, peek_name(s1)));
        restore_ids();
        let r = f(a0, s1, s2, s3, 0, 0, 0, 0);
        log("REMATCH: request placed");
        return r;
    }

    // Remember every match request the game makes (character select -> match).
    if name_a == "IngameCallSequenceScene" && a3 != 0 {
        capture_snapshot(a1, a2, a3);
        take_region_snapshot();
        log("saved the match request");
    }
    f(a0, a1, a2, a3, a4, a5, a6, a7)
}

fn install_enq_hook(base: usize) {
    BASE_ADDR.store(base, Ordering::Relaxed);
    unsafe {
        A64HookFunction((base + (ENQ_GHIDRA - GHIDRA_BASE)) as *const c_void, hook_enq as *const c_void, ORIG_ENQ.as_ptr());
    }
    log("scene request hook installed");
}

// ---- Controller hook -------------------------------------------------------------------------
unsafe fn hide_buttons(state: *mut NpadHandheldState, kind: usize) {
    (*state).Buttons &= !(KEY_A | KEY_B | KEY_L | KEY_R | KEY_ZL | KEY_ZR | KEY_PLUS);
    if kind == 5 {
        // GameCube: the analog triggers too (4 bytes each at byte 36 and 40)
        let p = (state as *mut u8).add(36) as *mut u32;
        *p = 0;
        *p.add(1) = 0;
    }
}

// The main combo (L/ZL + R/ZR + A + Start) = rematch. The same combo with B also held = the old restart
// (hidden results stage). A short wait tells them apart, so pressing B a moment after the rest still counts.
unsafe fn handle_combo(raw: u64, prev: u64, now: u64, ready: bool) {
    let cp = COMBO_PEND.load(Ordering::Relaxed);
    if cp == 0 {
        if ready && combo_held(raw) && !combo_held(prev) {
            COMBO_PEND.store(now + 1, Ordering::Relaxed);
            COMBO_SECRET.store(if raw & KEY_B != 0 { 1 } else { 0 }, Ordering::Relaxed);
        }
        return;
    }
    if raw & KEY_B != 0 {
        COMBO_SECRET.store(1, Ordering::Relaxed);
    }
    let secret = COMBO_SECRET.load(Ordering::Relaxed) != 0;
    let waited = now.saturating_sub(cp - 1);
    if secret || waited >= SECRET_WAIT_MS.load(Ordering::Relaxed) || !combo_held(raw) {
        COMBO_PEND.store(0, Ordering::Relaxed);
        let (act, enabled) = if secret {
            (ACT_RESTART, ENABLE_RESTART.load(Ordering::Relaxed) != 0)
        } else {
            (ACT_REMATCH, ENABLE_REMATCH.load(Ordering::Relaxed) != 0)
        };
        if enabled && ACTION.compare_exchange(ACT_NONE, act, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
            HIDE_UNTIL.store(now + HIDE_MS.load(Ordering::Relaxed), Ordering::Relaxed);
        }
    }
}

unsafe fn on_state(kind: usize, state: *mut NpadHandheldState, id: *const u32) {
    let id = if id.is_null() { 0 } else { (*id & 63) as usize };
    let slot = kind * 64 + id;
    let raw = (*state).Buttons;
    let prev = PREV[slot].swap(raw, Ordering::Relaxed);
    let now = now_ms();

    // Right after we trigger something, keep these buttons away from the game for a moment.
    if now < HIDE_UNTIL.load(Ordering::Relaxed) {
        hide_buttons(state, kind);
        PEND[slot].store(0, Ordering::Relaxed);
        return;
    }

    let since = RESULTS_SINCE.load(Ordering::Relaxed);
    if since == 0 || !in_results() {
        PEND[slot].store(0, Ordering::Relaxed);
        COMBO_PEND.store(0, Ordering::Relaxed);
        return;
    }
    let age = now.saturating_sub(since - 1);
    let ready = age >= MIN_RESULTS_MS.load(Ordering::Relaxed);

    // Any shoulder button held on the results screen: keep A, B and Start away from the game. A lone
    // A press would advance the results screen and take its scene away before our call runs.
    if raw & (KEY_L | KEY_R | KEY_ZL | KEY_ZR) != 0 {
        (*state).Buttons &= !(KEY_A | KEY_B | KEY_PLUS);
    }

    handle_combo(raw, prev, now, ready);

    if lr_held(raw) {
        // Shoulders held on results: Start is part of the combo, never a "skip".
        PEND[slot].store(0, Ordering::Relaxed);
        (*state).Buttons &= !KEY_PLUS;
        if combo_held(raw) {
            (*state).Buttons &= !(KEY_A | KEY_B); // the combo's A (and B) should not reach the results screen
        }
        return;
    }

    // Start on its own. A short wait (or its release) tells it apart from the start of the combo.
    let pend = PEND[slot].load(Ordering::Relaxed);
    if pend == 0 {
        if raw & KEY_PLUS != 0 && prev & KEY_PLUS == 0 {
            PEND[slot].store(now + 1, Ordering::Relaxed);
        }
    } else {
        let held_ms = now.saturating_sub(pend - 1);
        if raw & KEY_PLUS == 0 || held_ms >= START_HOLD_MS.load(Ordering::Relaxed) {
            PEND[slot].store(0, Ordering::Relaxed);
            if ready && ENABLE_EXIT.load(Ordering::Relaxed) != 0 {
                if ACTION.compare_exchange(ACT_NONE, ACT_EXIT, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
                    HIDE_UNTIL.store(now + HIDE_MS.load(Ordering::Relaxed), Ordering::Relaxed);
                }
            }
        }
    }
}

macro_rules! make_hook {
    ($name:ident, $kind:expr, $ty:ty) => {
        unsafe extern "C" fn $name(state: *mut $ty, id: *const u32) {
            let orig = ORIG[$kind].load(Ordering::Relaxed);
            if !orig.is_null() {
                let f: unsafe extern "C" fn(*mut $ty, *const u32) = std::mem::transmute(orig);
                f(state, id);
            }
            on_state($kind, state as *mut NpadHandheldState, id);
        }
    };
}
make_hook!(hook_fullkey, 0, NpadHandheldState);
make_hook!(hook_handheld, 1, NpadHandheldState);
make_hook!(hook_joydual, 2, NpadHandheldState);
make_hook!(hook_joyleft, 3, NpadHandheldState);
make_hook!(hook_joyright, 4, NpadHandheldState);
make_hook!(hook_gc, 5, NpadGcState);

fn install_hooks() {
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

fn load_config() {
    let path = "sd:/results_control_v2.txt";
    match std::fs::read_to_string(path) {
        Ok(text) => {
            for line in text.lines() {
                let mut parts = line.splitn(2, '=');
                if let (Some(key), Some(val)) = (parts.next(), parts.next()) {
                    if let Ok(n) = val.trim().parse::<u64>() {
                        match key.trim() {
                            "min_results_ms" => MIN_RESULTS_MS.store(n, Ordering::Relaxed),
                            "start_hold_ms" => START_HOLD_MS.store(n, Ordering::Relaxed),
                            "hide_ms" => HIDE_MS.store(n, Ordering::Relaxed),
                            "enable_restart" => ENABLE_RESTART.store(n, Ordering::Relaxed),
                            "enable_exit" => ENABLE_EXIT.store(n, Ordering::Relaxed),
                            "enable_rematch" => ENABLE_REMATCH.store(n, Ordering::Relaxed),
                            "secret_wait_ms" => SECRET_WAIT_MS.store(n, Ordering::Relaxed),
                            "swap_at_unlock" => SWAP_AT_UNLOCK.store(n, Ordering::Relaxed),
                            "restore_ids" => RESTORE_IDS.store(n, Ordering::Relaxed),
                            _ => {}
                        }
                    }
                }
            }
        }
        Err(_) => {
            let _ = std::fs::write(
                path,
                "min_results_ms=3500\nstart_hold_ms=100\nhide_ms=1000\nenable_restart=1\nenable_exit=1\nenable_rematch=1\nsecret_wait_ms=120\nswap_at_unlock=1\nrestore_ids=1\n",
            );
        }
    }
    log(&format!(
        "config: min_results_ms={} start_hold_ms={} hide_ms={} enable_restart={} enable_exit={} enable_rematch={} secret_wait_ms={} swap_at_unlock={} restore_ids={}",
        MIN_RESULTS_MS.load(Ordering::Relaxed),
        START_HOLD_MS.load(Ordering::Relaxed),
        HIDE_MS.load(Ordering::Relaxed),
        ENABLE_RESTART.load(Ordering::Relaxed),
        ENABLE_EXIT.load(Ordering::Relaxed),
        ENABLE_REMATCH.load(Ordering::Relaxed),
        SECRET_WAIT_MS.load(Ordering::Relaxed),
        SWAP_AT_UNLOCK.load(Ordering::Relaxed),
        RESTORE_IDS.load(Ordering::Relaxed)
    ));
}

#[skyline::main(name = "results_control_v2")]
pub fn main() {
    let _ = now_ms();
    log("results_control_v2 loaded");
    std::thread::spawn(|| {
        // Wait for the game to finish starting up.
        std::thread::sleep(Duration::from_secs(20));
        load_config();

        let base = unsafe { getRegionAddress(Region::Text) as usize };
        let (pos, count) = match unsafe { find_pattern(base) } {
            Some(x) => x,
            None => {
                log("byte pattern NOT found; staying idle (the game version may differ)");
                return;
            }
        };
        log(&format!("pattern found at {} ({} matches)", gh(base + pos, base), count));
        let global_off = match unsafe { decode_global(base, pos + ADRP_AFTER_PATTERN) } {
            Some(o) => o,
            None => {
                log("could not decode the global pointer; staying idle");
                return;
            }
        };
        let global = base + global_off;
        log(&format!("game state global is at {}", gh(global, base)));

        let mut fm: usize = 0;
        unsafe {
            LookupSymbol(&mut fm, "_ZN3lib9SingletonIN3app14FighterManagerEE9instance_E\0".as_ptr());
        }
        FM_ADDR.store(fm, Ordering::Relaxed);
        install_hooks();
        install_enq_hook(base);

        let table_expected = base + (TABLE_GHIDRA - GHIDRA_BASE);
        let mut was_results = false;
        let mut locked = false; // after a call, wait for the results screen to go away
        let mut locked_at = 0u64;
        loop {
            let results = unsafe { in_results() };
            let now = now_ms();
            if results && !was_results {
                RESULTS_SINCE.store(now + 1, Ordering::Relaxed);
                log("results screen began");
                unsafe { log_region_diff("results began"); }
            } else if !results && was_results {
                RESULTS_SINCE.store(0, Ordering::Relaxed);
                ACTION.store(ACT_NONE, Ordering::Relaxed);
                locked = false;
                log("results screen ended");
            }
            was_results = results;
            if locked && now.saturating_sub(locked_at) > 8000 {
                locked = false; // safety: never stay locked forever
            }

            unsafe { watch_ids(); }
            let armed = ARMED_UNTIL.load(Ordering::Relaxed);
            if armed != 0 && now + 1 > armed {
                ARMED_UNTIL.store(0, Ordering::Relaxed);
                log("REMATCH: the game never asked for a next scene in time; gave up");
            }

            let act = ACTION.load(Ordering::Relaxed);
            if act != ACT_NONE {
                if !results || locked {
                    ACTION.store(ACT_NONE, Ordering::Relaxed);
                } else {
                    // Follow the chain, checking every step, then check it is the expected table.
                    let mut obj = 0usize;
                    let mut vtable = 0usize;
                    unsafe {
                        let l1 = *(global as *const usize);
                        if plausible(l1) {
                            let l2 = *(l1 as *const usize);
                            if plausible(l2) {
                                obj = *(l2 as *const usize);
                                if plausible(obj) {
                                    vtable = *(obj as *const usize);
                                }
                            }
                        }
                    }
                    let (name, idx, expected) = if act == ACT_RESTART {
                        ("RESTART", RESTART_INDEX, RESTART_GHIDRA)
                    } else if act == ACT_REMATCH {
                        ("REMATCH (leave results)", EXIT_INDEX, EXIT_GHIDRA)
                    } else {
                        ("EXIT TO STAGE SELECT", EXIT_INDEX, EXIT_GHIDRA)
                    };
                    if obj == 0 || vtable != table_expected {
                        log(&format!("{}: game state object/table not as expected ({}); not calling", name, gh(vtable, base)));
                    } else {
                        let entry = unsafe { *((vtable + idx * 8) as *const usize) };
                        if entry != base + (expected - GHIDRA_BASE) {
                            log(&format!("{}: table entry is {} not the expected function; not calling", name, gh(entry, base)));
                        } else {
                            let (s1, s2) = unsafe { (*((obj + 0x128) as *const u64), *((obj + 0x130) as *const u64)) };
                            let age = now.saturating_sub(RESULTS_SINCE.load(Ordering::Relaxed).saturating_sub(1));
                            log(&format!("{}: calling table entry [{}] ({}) on object {:#x} | state pair {:#x} {:#x} | {} ms into results", name, idx, gh(entry, base), obj, s1, s2, age));
                            let f: extern "C" fn(usize, usize, usize, usize, usize, usize, usize, usize) =
                                unsafe { std::mem::transmute(entry) };
                            unsafe { log_region_diff(name); }
                            if act == ACT_REMATCH {
                                if SNAP_OK.load(Ordering::Relaxed) != 1 {
                                    log("REMATCH: no saved match request yet (start a match from character select first); doing nothing");
                                    ACTION.store(ACT_NONE, Ordering::Relaxed);
                                    continue;
                                }
                                ARMED_UNTIL.store(now + 12000 + 1, Ordering::Relaxed);
                            }
                            f(obj, 0, 0, 0, 0, 0, 0, 0);
                            log(&format!("{}: call returned", name));
                            locked = true;
                            locked_at = now;
                        }
                    }
                    ACTION.store(ACT_NONE, Ordering::Relaxed);
                }
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    });
}
