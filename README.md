# Kaggiguy's Quality of Life Mod v1

Start-button skip, instant rematch and name tag swap for Super Smash Bros. Ultimate (Skyline plugins).

Two small offline quality-of-life plugins for Super Smash Bros. Ultimate on a modded Switch.
Tested on game version **13.0.4** only.

## results_control_v2: rematch from the results screen

On the offline results screen:

| Input | What happens |
|---|---|
| Start | Leave results straight to stage select (no A presses) |
| L/ZL + R/ZR + A + Start | **Rematch**: straight back into a new match, same stage, same fighters. No stage or character select |
| L/ZL + R/ZR + A + B + Start | Secret combo: restart into the hidden results stage (stage effects can vary with winning character) |

Any controller works. You can rematch as many times as you like in a row.

## tag_swap: change your name tag mid-match

During an offline match (also while paused), hold two shoulder buttons (L+R, ZL+ZR, or SL+SR on a
sideways Joy-Con) and press **D-pad Right or X** for the next tag, **D-pad Left or Y** for the previous
one. Each controller changes its own player's tag.

One press changes the name above the fighter and by the damage counter, that tag's saved controller
settings (button mapping, tap jump, ...), the name on the results screen, and the tag remembered for
the next character select. Players can't share a tag. Works for one to four players, and each controller changes its own player's tag even when players joined character select in a different order than their controller ports.

## Requirements

- Switch with Atmosphere, Skyline and ARCropolis, game version 13.0.4
- Offline play only. Not tested on emulators.

## Install

Download the zips from the Releases page (not the source code).

1. Copy the `atmosphere` folder from the zip onto the SD card (merge when asked).
2. Plugins end up in `sd:/atmosphere/contents/01006A800016E000/romfs/skyline/plugins/`.
3. Enjoy. Run it back! lol

## Optional settings

`sd:/results_control_v2.txt`, one `key=value` per line. The plugin creates this file with the defaults on first run:

| Key | Default | Meaning |
|---|---|---|
| min_results_ms | 3500 | Ignore inputs for this long after results appear (too low can crash the game if you mash right as a match ends) |
| start_hold_ms | 100 | How long Start must be held |
| hide_ms | 1000 | How long the combo's buttons are hidden from the game |
| enable_restart | 1 | Secret hidden-stage combo on/off |
| enable_exit | 1 | Start-alone exit on/off |
| enable_rematch | 1 | Main rematch combo on/off |
| secret_wait_ms | 120 | How long to wait for B before treating the combo as a plain rematch |
| swap_at_unlock | 1 | Internal: where the saved match request is swapped in |
| restore_ids | 1 | Internal: safety net that restores fighter ids |

Logs: `sd:/results_control_v2_log.txt` and `sd:/tag_swap_log.txt`. Send these with any bug report.

## Known limits

- 13.0.4 only. On another version the plugins check their addresses and stay idle instead of crashing.
- Rematch repeats the **last match you started from character select**. If you have not started one
  since boot, it logs "no saved match request yet" and does nothing.
- Tested with both plugins installed together on a Switch. Not yet tested: 5 or more human players.
- Not planned: a pause-menu entry for tag swap. Maybe later: Yes/No rematch popup, stage-only and
  character-only rematch.

## Building from source

`plugins/` holds both plugins, each its own cargo-skyline project (nightly Rust). In each plugin folder run
`cargo skyline build --release`; the `.nro` ends up under `target/aarch64-skyline-switch/release/`. Set `const DIAG: bool = true;` in results_control_v2 for
extra logging.

## Credits

- **HewDraw Remix** (HDR-Development): the byte-pattern method for finding the game state object, and
  the tag table / controller mapping layout. Licensed AGPL-3.0.
- **Ultimate Training Modpack**, **results-screen-skip** (jugeeya): reference for hooks and the
  results-screen check.
- **ARCropolis** (Raytwo), **Skyline** (skyline-dev), **skyline-rs** and **smash-rs** crates.
- Reverse engineering, testing and ideas: Kaggiguy.
