# The brief-inventory API (PR #118): notes

## Why

The user's "Everything" rule (2026-10-16): every definition a brief's route reads gets a
published equation before the brief is dispatched, found by a pre-ship inventory per brief.
The five briefs are:
- U2-S (`exists_selfStartupTMK`);
- the B6 F3 continuation (`exists_configWindowRunnerTM`);
- B6 F5 (the ruler device);
- the canonizer's continuation 6 (`exists_canonGrammarStage`);
- **the §13d G4 continuation** (`exists_zoneExtendTM`, `exists_zoneRebalanceTM`; second commit).

The first four were inventoried at #116's head, which is the tip's Lean content after #116
merged; G4's at #117's head (`98472df2`), against `oleans-lm11a`. This PR fills the gaps found.

## The inventory method

- **The elaborator.** A read-only command lists the `TCSlib` definitions (not theorems,
  instances, structures or inductives) occurring in the types of each brief's cited lemmas
  (`scripts/DefInventory.lean.txt`; a per-lemma variant in `scripts/DefInventoryEach.lean.txt`).
  The cited lemmas are each brief's import probe:
  - U2-S: the re-measured issue probe, 85 names (`probes/U2SImportProbe-issue.lean.txt`);
  - F5: its 40-name probe;
  - F3: its 54-name probe plus the record and patch lemmas;
  - cont6: cont4's 130-name list, which its brief cites.
- **Crossed with lint check 8.** The output (`inventory/*-inventory.out`) is crossed with check 8's
  list of definitions that have no lemma beside them (`logs/lint-tip.txt`).
- **Judged against each route.** A definition the route only mentions, carried as an opaque term,
  needs no equation. One the worker must compute through does.

| Flagged | Brief | Judgment |
|---|---|---|
| `bufferedCompTM` (`k`, `State`), `universalPrefixTM`, `prefixCanonTM` | U2-S | **gap**: the startup places the prefix canonizer in a host, which needs its tape count. `prefixCanon_run` states its configuration over `bufferedSecondCfg universalPrefixTM F`, whose tapes are `Fin (universalPrefixTM.k + (1 + F.k))`. Check 8 passes `bufferedCompTM` (it has lemmas) but none gives its fields. |
| `VirtualTag` | U2-S, F5 | **gap** (an `_iff`): F5's virtual-input rows carry tag hypotheses. U2-S needs it only if it cites `bufferedSecondCfg_run` directly. |
| `vhostBuffer`, `vhostBank` | F5 | **gap**: tape indices of the virtual-input host |
| `RecSym.digitEmb` | F3 | **gap**: relating lifted cells to digits |
| `posWidth`, `binDigits` | F3 | `posWidth` is read through `record_pos_lt` and `recordLength_eq`. Both equations are added for completeness, since the file is edited. |
| `counterLoopBody` | cont6 | **gap**: the round-contract counter loop's trajectories (`RoundContract.counterLoopDone_traj`/`Escape_traj`) |
| `stateWord` | cont6 | **gap** (cheap): the call rows' statements |
| `decFixed` | #117, MIG-12 | **gap**: the decrement contract's precondition is `decFixed w = some v` |
| `tapeAction`, `inputMoveAction`, `catalogTrace` | all | covered: `step_of_tapeAction_move`/`_write`, `step_of_inputMoveAction`, `catalog_trace_run` (check 8's naming heuristic misses them) |
| `Complexity.LogProg.simCfg`, `stg`, `wr`, `PB`, `markI` (Hydroxyi's) | U2-S | not needed: they occur only in the stage lemmas (`sim_step_clean`, `stages_run`). U2-S's route reads `cleanTM_run`, whose statement uses only `cleanTM` and the configuration basics (`inventory/U2S-per-lemma.out`). |
| `tableBitsK`, `actionBitsK`, Encoding's bit words | U2-S, cont6 | opaque in the cited statements: `serializeK_eq`'s right side, and `codeActionK_length`'s bound |
| `StepBlock.Rep`, `SkipPh`, `exit`, `workReadsK`; `codeSkipActionK`/`Fin`/`State`/`Table2` | cont6 | not in cont6's route: they come from cont4's broader list (the step block's loop, the eraser, the two-tape table; `inventory/C6-per-lemma.out`) |
| `Round`, `Segment`, `HeadBox`, `Cfg.SameOutside`, `Contract.Traj` | G4 | **gap** (`_iff`s): the rebalance scan iterates rounds with two escapes and a head relation, which `Round.of_cut` (one escape, trivial relation) cannot build. So the worker constructs `Round` and `HeadBox` facts and reads `Segment`s, frames and trajectories |
| `roundOrbit` | G4 | **gap** (cheap): `roundOrbit_succ` is published, but not round `0` |
| `RoundContract.hullLo`, `hullHi` | G4 | **gap** for completeness: they are the envelope of `RoundContract.release`, the route's single-index iteration host |
| `Cfg.bindState` | G4 | **gap**: `Contract.inPhase_post` is stated through it, and the route composes by `inPhase` |
| `Contract.Positive`, `roundStop`, `Contract.Frames` | G4 | covered: `positive_of_not_mem`/`not_mem_of_positive`, `not_mem_roundStop`, `frames_iff` (check 8's heuristic misses the first two) |
| `scanMap`, `scanShift`, `mealyRun` | G4 | covered for the route: the re-packing scan reads them through `scanResult_map`, `scanResult_shiftRight` and `scanResult_shiftLeft` (`scanTM_contract_post` is stated through `scanResult`) |
| the zone layer, the row contracts, `framedContract`, `seekPost`, `sweepPost`, the combinators | G4 | covered by #112 and #116: every contract and combinator the route names has its five field equations (`inventory/G4C-enum.out`). The partial's helpers that unfold `zonedTape`, `zoneSlotOf` and `zoneCapacity` re-point to `zonedTape_zero`/`_of_pos`/`_of_neg`, `zoneSlotOf_inr` and `zoneCapacity_eq` |

## What

The patch is `brief-api.patch`: one commit, `277735f2`, on #117's head `1358ff73` (stacked).
All declarations are added; no `@[simp]`; every docstring states its formula.
- **`Simulation`:** `bufferedCompTM_k`, `bufferedCompTM_State` (`simps`, `isSimp := false`);
  `VirtualTag_iff`.
- **`UniversalStartup`:** `universalPrefixTM_k`, `universalPrefixTM_State` (`simps`);
  `prefixCanonTM_eq`.
- **`Build/VirtualInput`:** `vhostBuffer_eq`, `vhostBank_eq`.
- **`Build/CfgRecord`:** `RecSym.digitEmb_apply`, `binDigits_eq`, `posWidth_eq`.
- **`Build/CounterLoop`:** `counterLoopBody_{state,inputPos,workTapes,workTapePos,output}`
  (`simps`); `decFixed_nil`, `decFixed_true_cons`, `decFixed_false_cons`.
- **`Build/Loop`:** `stateWord_eq`.

**Second commit `36325650` (the G4 continuation), `brief-api-2.patch`:**
- **`Build/Contract/Basic`:**
  - `Cfg.sameOutside_iff`, `headBox_iff`, `segment_iff`, `round_iff`, `Contract.traj_iff`, each
    `Iff.rfl`;
  - `roundOrbit_zero`;
  - `RoundContract.hullLo_eq`, `hullHi_eq`.
- **`Build/Contract/Seam`:** `Cfg.bindState`'s five field equations (`simps`, `isSimp := false`).
- The method is the same: `inventory/G4C-inventory.out` (the 94 names of G4's probe),
  `G4C-fields-inventory.out` (the 260 published lemmas its route can read, from
  `scripts/EnumLemmas.lean.txt`), and `G4C-enum-rounds.out`.
- The statements behind the "covered" judgments are printed by `probes/G4CoveredProbe.lean.txt`
  at `4ae686be` against `oleans-lbapi2` (`inventory/G4C-covered-probe.out`, 0 errors).

## Checks (maintainer, against `oleans-lm11a`)

- **Elaboration** (`logs/elab-*-head.out`): 0 errors in all six files, with warnings equal to the
  base. `UniversalStartup` (6) and `Loop` (66) were compared by `warndiff` against their
  unchanged elaborations (`logs/elab-*-base.out`), with no new warning; `Simulation` has 1 as at
  the base; the other three have 0.
- **Generated names and axioms** (`logs/probe-*.out`): the 9 generated equations resolve; the 11
  hand-written theorems print standard axioms only (corrected at the gate, finding 3; this said
  15).
- **Freeze** (`logs/freeze.log`): publics added only, in all six files.
- **Lint** (`logs/lint-head.txt`): 0 FAIL, 68 WARN over 79 files. Check 8 adds no name and drops
  10 (168 → 158 in `TuringMachine/`).
- **Screen** (copy-text v3; `logs/screen-{base,head}.txt`, `logs/screen-delta.log`; the population
  is the six files, `logs/screen-population.txt`; base #117's `1358ff73`): 404 → 404 declarations,
  167 → 167 pairs, 0 new at the head.
  - The count does not grow because the screen skips bodies under 60 characters (outside
    whitespace). Every new theorem's body is 3 to 7 characters (`rfl`, `Iff.rfl` and the like;
    `logs/screen-bodylen.txt`), and `simps` attributes are not declarations.
- **Replay:** `replay-lbapi.sh`, the six files' downstream closure at the stacked head
  (311 modules), from `oleans-lm11a`. **Passed (user, 2026-10-16):** 311 of 311, 0 failed
  (`replay-lbapi.log`, at `277735f2`). The per-module sorry counts equal a static count
  (0 mismatches, 94 in total; `replay-lbapi-static.txt`), as at #116.

## Checks of the second commit (maintainer, against `oleans-lm11a`; `logs/g4/`)

The two files are identical at `1358ff73`, `98472df2` and `277735f2`, so they were developed and
checked in a worktree at #117's head. The patch applied to #118's head gives a byte-identical diff.
- **Elaboration:** `Contract/Basic` and `Contract/Seam`, 0 errors and 0 warnings, as at the base.
- **Generated names and axioms** (`elab-Probe*-head.out`): the 13 names resolve, with standard
  axioms or none.
- **Freeze** (`freeze.log`): 8 publics added in `Basic`, none removed; `STATEMENT CHANGED: []` in
  both. The `simps` equations are attribute-generated.
- **Lint** (`lint-head.txt`): 0 FAIL, 68 WARN over 79 files (69 at the base). Check 8 drops 6
  names: `Basic` keeps only `roundStop` (covered by `not_mem_roundStop`), and `Seam` has no WARN.
  No added line is over 100 characters.
- **Screen** (`screen-{base,head}.txt`, `screen-delta.log`; the two files): 68 → 71 declarations,
  21 → 28 pairs, 9 new and 2 gone. **None is copied text.**
  - The screen runs a declaration's text up to the next declaration, so an `Iff.rfl` lemma placed
    before a `namespace`/`section` opening takes in the opening's `variable` line.
  - Every new pair's shared text is exactly such a binder line (`screen-pairtext.txt`, with the
    screen's own segmentation, `scripts/pairtext.py.txt`).
  - The two gone pairs are the same artifact: `Traj` no longer takes in `section TrajBasic`'s
    line.
- **Chained replay** `replay-lbapi2.sh`: the two files' downstream closure at `36325650`
  (86 modules, all within the first replay's 311), from `oleans-lbapi`. **Passed (user,
  2026-10-16):** 86 of 86, 0 failed (`replay-lbapi2.log`). The sorry counts equal a static count
  (0 mismatches, 56 in total; `replay-lbapi2-static.txt`).

## Up to date with the tip

#117 merged (user, 2026-10-16; `bd1ae147`). The head `4ae686be` merges the tip. Its Lean differs
from the replayed `36325650` only in #117's gate correction of `counterRowContract`'s docstring
(`98472df2`), which #117's gate re-elaborated (0 errors, 0 warnings). The replays therefore cover
the head's Lean, and the snapshot `oleans-lbapi2` serves the tip after #118.

## The gate, round 1, and round 2 (2026-10-16 and 17)

**Round 1: FAIL, 0 blockers, 2 majors, 1 minor** (`audits/brief-api-findings.md`; resolutions
`audits/brief-api-resolutions.md`; the review `r2/gate-review.md`).
- **Findings 1 and 2** were cont6's: `codeSkipRepeat`'s two cases, and the field equations of
  the two round-contract counter loops.
- **Finding 3** was the count above.
- The inventory method missed the cited definitions themselves. The seed-inclusive elaborator
  (`r2/probes/DefInventorySeeds.lean.part.txt`) re-ran all five briefs and found N1:
  `Cfg.mapState`'s and `Action.mapState`'s fields.

**Round 2 (`lean/brief-api` at `4624fc05`):**
- MIG-12's API (`9872634e`, fast-forwarded; its replay passed, 160 of 160);
- `88fb25f3` (findings 1 and 2);
- `4624fc05` (N1).

The checks are in `r2/logs/` and `r2/review-out/`; the replay `replay-lbapi3.sh` covers 274
modules from `oleans-lm12api`.
