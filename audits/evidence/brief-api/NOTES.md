# The brief-inventory API (PR #118): notes

## Why

The user's "Everything" rule (2026-10-16): every definition a brief's route reads gets a
published equation before the brief is dispatched, found by a pre-ship inventory per brief.
The four drafted briefs are:
- U2-S (`exists_selfStartupTMK`);
- the B6 F3 continuation (`exists_configWindowRunnerTM`);
- B6 F5 (the ruler device);
- the canonizer's continuation 6 (`exists_canonGrammarStage`).

They were inventoried at #116's head, which is the tip's Lean content after #116 merged. This PR
fills the gaps found.

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

## Checks (maintainer, against `oleans-lm11a`)

- **Elaboration** (`logs/elab-*-head.out`): 0 errors in all six files, with warnings equal to the
  base. `UniversalStartup` (6) and `Loop` (66) were compared by `warndiff` against their
  unchanged elaborations (`logs/elab-*-base.out`), with no new warning; `Simulation` has 1 as at
  the base; the other three have 0.
- **Generated names and axioms** (`logs/probe-*.out`): the 9 generated equations resolve; the 15
  hand-written theorems print standard axioms only.
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
  (311 modules), from `oleans-lm11a`. The user runs it.
