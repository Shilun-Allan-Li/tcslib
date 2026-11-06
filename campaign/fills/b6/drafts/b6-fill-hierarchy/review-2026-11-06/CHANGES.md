# Changes to the H fill brief (review 2026-11-06 applied)

Source: `campaign/fills/b6/drafts/b6-fill-hierarchy.DRAFT.md`. Output: `b6-fill-hierarchy.DRAFT.md`
here. Probe: `wt-hk/rvprobe/hrework/HImportProbe2.lean` (171 checks, 86 axiom prints), output
`HImportProbe2.out` here.

## Review findings (one line each)

- **B1:** applied. The radius is bound to `embedSilentRetTM ι cap (M_g.tm.liftSymbols e)` with
  `embedSilentRetTM_run`, the readings `embedSilentCfg_cap`/`_unselected`/`_selected_tape`/`_pos`
  and the `simps` state/inputPos/output equations, the space lemmas
  (`embedSilentRetTM_visitedByTapeHead`, `embedSilentTM_visitedByTapeHead`, `_frame`,
  `embedSilentTM_spaceUsedByTape_cap`), the lift's `runFrom`/`initCfg`/`spaceUsed` and field
  equations, `RecSym.digitEmb_apply`, `FinTM.bufferTape_nil`. `capture_run` and
  `capture_visitedByTapeHead` are named as not to be used (`captureCfg` has no reading).
  `Contract.liftSymbols` is noted as not applicable. Rule 7 now bans a second "tape embedding or
  capture transformer" and names `embedSilentRetTM` as the one to use. `Build/Embed` was added to
  the probe and to the population. All of these elaborate.
- **M1:** applied. The `Bool` seam space corollaries are marked "do not apply". Bound instead:
  `seamCompTM_run_ofCfg`, `_firstReturn_ofCfg`, `_visitedByTapeHead_ofCfg`,
  `seamCompTM₂_run_ofCfg`; R1 (`embedEmitTM`, `_runFrom`, `_frame`, `embedEmitCfg_eq`/`_select`,
  `_selected_tape`/`_pos`, `_unselected`, `Cfg.select`); the `Contract` layer (`seq`, `embed`,
  `within`, `spaceUsedByTape_le`). The space route is named (visited-set unions, or envelopes via
  `spaceUsedByTape_le_card_Icc`/`spaceUsed_le_of_abs_le`, summed by `spaceUsed_eq_sum`). A tape
  plan was added; its blank-bank constraint (`WindowClock.lean:1512`) is binding. Checkpoint 2
  now says "a `Turing.Contract` or the `_ofCfg` run lemmas".
- **M2:** applied.
  - Input rewind: `(inputRewindTM 0).liftSymbols e` by R1 along `Fin 0 ↪ Fin K_D`, after a
    one-step right move of the fill's own (`step_of_some`, `moveInputPos_pos_of_ne_right`,
    `moveInputPos_rightBoundary`). This covers position 0.
  - Radius tape: `rewindTM_run_ofCfg` at `n = |ws|`. `skipBackTM` does not fit, because the head
    is not one blank past the word.
  - Verdict: `exists_recordTestTM` with the review's `P`, `windowRun_stop_unique`, `true` on
    `exhausted` without the test, and a one-step emitter leaf.
  - Readings: `initCfg_eq`, `Cfg.inWindow_init` (it holds at every radius, not only for small
    `g n`), `spaceUsed_le_of_halt`, `recordAt_iff`, `recordLength_eq`, `posWidth_eq`,
    `length_bits_le_log`, `length_pairEncode`, `length_bits_le_self`. Also added
    `joinFields_cfgRecord_length`, which the test's bound needs.
  - All of these are in the probe.
- **M3:** applied. `T := Fin 3`, `upd := summaryTag` and `hupd := summaryTag_none` are binding.
  The verdict goes through `outSummaryCode_eq_one_iff`, and `τ₀ = 0` through
  `outSummaryCode_nil`. There is also a pitfall line.
- **M4:** applied. Cite `exists_codeTM_spaceUsed` (`Encoding.lean:741`) and
  `MachineCode.decode_encode`. The `relabelState_runFrom_init` route is forbidden (rule 5).
- **M5:** applied per the user's ruling. Checkpoint 8 is kept and may end in a named escalation.
  It stops on that item only and states the missing lemma; the first two targets do not depend on
  it.
  - Correction to the ruling's premise: the padding map's polynomial time is **published**. With
    the pad `(|x| + 1)^2` it is `polyTimeComputable_id.pairEncode (polyTimeComputable_polyUnary
    1 2)`.
  - Partial hosts named for the decider: `FinTM.exists_inputCallTM` at
    `computesFunInTime_pairFst` (time only; space via `spaceUsed_le_mul_succ`), and Z1's
    `vhostEmitTM` with `_runFrom`, `_spaceUsed_le` and `vhostCfg_workTapes`.
  - Escalation now narrowed to: the pad-length test in `O(|y|)` space, and the assembly.
  - The extraction facts are stated: `pairEncode_injective`, `A(n+1) ≤ n²+1` for `n ≥ A+1`, and
    `spaceConstructible_poly 2 (by norm_num)`.
- **m1:** applied. All four copied lemmas are renamed `sph_*`. Rule 11 says "every private …
  the copied `hr_*` included".
- **m2:** applied. The `logSpace_le_succ` instruction is dropped. The pre-ship summary now says it
  closes in the duplication probe but the route does not need it.
- **m3:** applied.
  - Fixed line numbers: `space_hierarchy`'s docstring starts at 163; region (b) ends before 163;
    "read first" is 163–313; "spec, fill pending" is 274 and "of phase P4.1" is 279.
  - Region (d) now lists every label line by line: module docstring 22–28, 48, 58, 61–65, 67;
    the targets' H2/H3/H5, R8.5d, O6, O4, W1, R8.0b, round/finding, row 17/18, P0 and P4.1.
  - Ruled in scope, except `space_universal`'s docstring and its main-results entry (69–70),
    which are F6's.
- **m4:** applied. The base is the campaign after #175, #177, #181, #191, #196, #202 and #207
  (`d43a1374`). The header's "issues after #181" is gone.
- **m5:** applied. `SavitchARM/Deepen` is "new and not in your order list"; `Savitch` is in it.
- **m6:** applied. The population is 27 files, with `TimeHierarchy/Diagonal` counted as cited.
  The 16 modules the revision newly cites are added (43 in all). The fill's own before-screen is
  its base for new pairs, and the pre-ship's 27-file base numbers are kept.
- **m7:** applied. `mem_NP_iff_exists_length_le`, `PolyTimeReducible` and the other `NP` and
  padding names are now in `HImportProbe2`. The "Cited infrastructure" section separates the 72
  from the 99 added.
- **m8:** applied. `WindowClock.lean:1503` and `RecordTable.lean:5805` are in the brief. The
  route note (tracked) still says 1506/5809, and the brief says it governs where they differ. I
  did not edit the note.
- **m9:** applied. The route probe has four lemmas and three axiom prints (none for
  `hr_sq_le_two_pow`). Rule's axiom-print requirement covers `sph_sq_le_two_pow`.
- **m10:** applied. `A := C_α (c₁ · c₀ + c₁ + 1)`, with `c₁` the normal form's constant, `C_α`
  from `exists_selfUniversal`, and `c_D` the packaging constant.
- **m11:** applied. The seal list names the five once, then the revision's transports and record
  definitions.
- **n1:** applied. After each edit, check `Hierarchy` plus its only importer, the facade. The
  final sweep keeps the 52-module tail.
- **n2:** applied. `L_D` is defined through `D`'s output (`MultiTapeTM.indicator`), not through
  `windowRun`. This is in the packaging bullet.
- **n3:** no change needed (the review confirms the mathematics). The constants named in it are
  now explicit in the route (`c₁`, `C_α`, `spaceUsed_le_of_halt`).

## Other changes and process notes

- Title: the draft's title line was over 100 characters. It is now a short title plus a
  "Targets:" line.
- **#209 has merged** (`5761d6e0`, `NTimeHierarchy`'s docstring only; not in the order list).
  "In flight" now lists only #208, with a note that #209 changes nothing in the closure.
- Pre-ship numbers are kept as measured (72/0, 4 sorry lines, 5 sealed / 9 controls, 6/2
  `exact?`, 220/63/26/10, 1,345/740/207,247, lint 0/80/111). Only the population count changed
  (28 to 27).
- **Probe run deviation:** `oleans-lcamp1` does not exist on this machine (run 1 failed with
  "unknown module prefix"; the output was overwritten).
  - Runs 2 and 3 used `oleans-lnth`, the campaign's snapshot after #209 per HANDOFF; its closure
    equals `d43a1374`'s, because #209 touches only `NTimeHierarchy`.
  - Run 3 is the shipped output: exit 0, 0 errors.
  - All 86 axiom prints are within `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
    Among them are `exists_inputCallTM`, `polyTimeComputable_polyUnary` and the Z1 lemmas.
- The probe file also needs to be copied into the round's inputs as `HImportProbe2.lean.txt`
  before issue. The brief cites it there.
