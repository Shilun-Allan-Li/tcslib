# Gate 03l clean-up, part 1: report

(Saved by the maintainer from the worker's hand-back message; the worker could not write this file.)

- **Base:** `0c348ff94cacf24d96d99078c9dd9e328530c8d2` (head of `wt-g03c-fix`, the combined gate 03a + 03c repair).
- **Branch:** `wip/g03l-cleanup` in worktree `scratchpad/wt-g03l-fix`. Nothing was pushed by the worker.
- **Olean tree:** `scratchpad/g03l-oleans`.
- **Logs:** `scratchpad/g03l-fix/`.

## Commits (oldest first)

```
dd5be2eb7dc1e7232712b66854c6f97739f70144 Gate 03l clean-up A: harvest the clean-module host (DL-16, R-03l-1)
b636dd20c79736daf5a7c6edad0336c0cbfce9ef Gate 03l clean-up B: UnaryMul uses PairSplit's parser (DL-18)
2221e90210bddcaddd3760565ddb75915a247cb0 Gate 03l clean-up C: rename StateLoop.BlockLoop to BlockMapLoop (DL-19)
29e02fe26f2c521e35590dcaea817fb30c5d4def Gate 03l clean-up D: polyTimeComputable_stateFind public (DL-11, first half)
43e8fe2c27c54c2c50e01541024995e95c6bf6fa Gate 03a finding 3: add NUPPT.exists_compParam (item H)
84acb0c62986d092087b844e4d0b186c05719eee Gate 03l clean-up E: reading lemmas for the 03l definitions; re-point sites
9577890204d71f78d88065b674bd8c73d4fdf785 Gate 03l clean-up F: statement docstrings (gate 03l minor 4)
f29be161cd86cfc3a9c38bd203bfa095b4974086 Gate 03l clean-up G: DESIGN §2.6 as-built erratum; Repetition prose (minor 2)
```

17 files, +1575 / −1415.

## Items

**A. The clean-module host (DL-16).** New `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean` (548 lines, namespace `Turing.ModuleHost`; header credits Seyoon Ragavan, the author of `SAT.lean`). Generic in the modules `M : Fin n → FinTM Bool`, the host's control states `C` (`[Fintype C] [DecidableEq C]`), their transition table `ctrl`, the return map `ret` and the start state `q₀` (the last two added beyond the brief because SAT and IterateFind differ in them). Public: `Clean` (`clean_iff`; docstring states `0 < M.k` and the positive first halt), `State` (abbrev; `state_eq`), `entry` (`entry_eq`), `hostTM` (`@[simps (config := { isSimp := false }) k tm_q₀]`, plus `hostTM_step_inl`), theorems `clean_install`, `clean_emit`, `host_call`, `host_clean`, `guard_add`, and run lemmas `first_halt`, `live_prefix`, `request_budget`. Padding, release-flag stop, `clean_stop`, `bridge_bound`, `host_seam` private. `host_call`/`host_clean` now guarantee no control state is visited (`∀ v < t, ∀ c : C, …`), specialized by each consumer.
- `ClassNP/SAT.lean` (+67 / −404): the 26-declaration private layer deleted; the emitter instantiates the host with `C = Unit`, private `satHostRet`, private `satHostCtrl`. No public statement changes; 81 warnings vs 83 at base (both removed ones were in the deleted copy).
- `Randomized/Build/IterateFindHost.lean` (695 → 362 lines): keeps `copyTM` (`simps k`), `hostCtrl` (`hostCtrl_eq`), `hostRet` (five case lemmas), `hostTM` (now an abbrev over `ModuleHost.hostTM`, `hostTM_eq`), `host_dispatch`/`host_branch`/`host_halt` through `hostTM_step_inl`.
- `IterateFind.lean` uses the public host; its private `request_budget` deleted.
- Renames: `IterateFind.Clean` → `Turing.ModuleHost.Clean`; `clean_install`, `clean_emit`, `guard_add` → `ModuleHost.*`; `HostState M` → `ModuleHost.State (Fin 3) M`; `hostEntry` → `ModuleHost.entry`; `host_call`, `host_clean` → `ModuleHost.*` (generalized); `hostRet` stays (type now `ModuleHost.State (Fin 3) M`); `hostTM` stays (abbrev). Only `IterateFind.lean` used them (`statements.md`).
- Records: registry row H14 in `machine-library-design.md` §14; facade `TuringMachine.lean` lists the module; Build `README.md` row; `TCSlib.lean` untouched.
- **Deviation (size):** +823 / −923 (1746 lines changed; tree shrinks by 100). 857 deletions are the two copies; 548 additions are the new file, mostly moved code. Read the "~1000 changed lines" limit as code written (823).

**B. `UnaryMul` uses `PairSplit`'s parser (DL-18).** `PairSplit.lean` publishes `Turing.PairParse`: `cfg` (simps field equations, `isSimp := false`), `cfg_inputSymbol`, `cfg_workTapeSymbols`, `cfg_congr`, `apply_cfg_stay`, `apply_cfg_advance`, `parse_first`, `parse_block`, `rewind_run`, each for every one-tape machine agreeing with the parser at its states (agreement as hypotheses, proved by `rfl` in each machine's own file). `UnaryMul.lean` deletes `mulCfg`, `mulCfg_read`, `mulCfg_congr`, `mul_first`, `mul_block`; `mul_back` is an instance of `rewind_run`. Deviation: three reading lemmas beyond the brief (`cfg_workTapeSymbols`, `apply_cfg_stay`, `apply_cfg_advance`), needed for the seal. Statements of `exists_pairSplitTM`, `exists_unaryMulTM` unchanged. `PairSplit.lean` 648 lines (INFO: over the 600 target).

**C. The name clash (DL-19).** `Complexity.StateLoop.BlockLoop` → `Complexity.StateLoop.BlockMapLoop` (`StringLoops.lean` 4 refs, `Repetition.lean` 8, `StateLoop.lean` prose 1); 17 declarations, statements kept.

**D. `polyTimeComputable_stateFind` public (DL-11, first half).** Statement unchanged; prose fixed in `Repetition.lean`, `StringLoops.lean`, `HardCoreLoops.lean:68`. Deviation: `ThreeColoring/Machines.lean:126` became ambiguous (opens `Complexity` and `EncodingMachines`); the call is qualified as `EncodingMachines.polyTimeComputable_stateFind` (no re-pointing). The copies' own "private" docstrings are left for part 2 (`EncodingMachines.lean:468`, `GI/Efficiency.lean:47, 83–84`, `GGMReduction.lean:258`).

**E. Reading lemmas (03l minor 3).** 38 lemmas (`blk_eq` unnecessary: `BlockMapLoop.blk` now private), none `@[simp]`, all `rfl`/`Iff.rfl` except `gstepBound_eval`: IterateFind `step_eq`; host `clean_iff`, `state_eq`, `entry_eq`, five `hostRet_*`, `copyTM_k`, `hostTM_k`, `hostTM_tm_q₀`; StateLoop `gstep_eq`, `gstepBound_eval`, `IterLoop.{start,step,acc,out}_eq`, `EmitLoop.{start,step,out}_eq`; StringLoops `MajLoop.{start,step,acc,out}_eq`, `XorLoop.{start,step,acc,out,rounds}_eq`, `EqLoop.{step,out,flag}_eq`, `BlockMapLoop.{start,step,acc,out,rounds}_eq`. Plus `hostCtrl_eq`, `hostTM_eq`, `hostTM_step_inl`. 18 sites re-pointed (16 of the review plus two in `polyTimeComputable_blockMap` reading `BlockMapLoop.rounds`, found by the seal).

**F. Docstrings (03l minor 4).** The 12 projection/test lemmas, `param_poly`, `host_clean`, `Clean`, note 65 (`stepWord_verdictWord`), and the six `orbit_eq` docstrings.

**G. Prose (03l minor 2).** Dated as-built erratum appended to DESIGN §2.6 (new-output guard with counterexample, actual-pair invariant, release-flag stop, padding, the host (H14), two-state copier, budget `A·(2n + 7 + P n)^D`, the `≤` counter test); §2.4 note (one work tape, shared parser). `Repetition.lean`'s construction plan and the sketch of `polyTimeComputable_iterateFind` describe the built route.

**H. `NUPPT.exists_compParam`** in `Randomized/Closure.lean`, statement exactly the review's; proved as `exists_comp` was; `exists_comp` re-derived as its special case (statement unchanged; its Scope paragraph points to the new theorem); docstring with tag `[PS10, §2.1, implicit; inventory Claim-26.3(a), (b)] (gate 03a, finding 3)`; `Checks.lean` print line added.

## Checks

1. Lint before (`lint-before.log`): 5 WARN on the six Build files, as expected.
2. Replay (`replay.log`, `replay-summary.txt`): 89 upstream modules of `SAT.lean`'s downstream (`up-build.log`) and 23 of the `TuringMachine` facade's closure (`tm-build.log`) built first, all rc=0; then 133 downstream modules and `Checks`: **134/134 rc=0, 0 errors**. Sorry warnings: the 112 modules in the base logs equal the base; of the 22 others, all 0 except `ClassPSPACE/TQBF` (21, unchanged main code, same in older logs); `Checks` 0.
3. Axioms (`axioms.log`): 268 public theorems of the 12 changed files with theorems: 157 `[propext, Classical.choice, Quot.sound]`, 69 `[propext, Quot.sound]`, 15 `[propext]`, 27 none; no `sorryAx`.
4. Seal (`seal.log`, `seal.py`): 8 consumer files pass sealed (`IterateFind`, `IterateFindHost`, `SAT`, `UnaryMul`, `Repetition` (27 loop definitions and `IterateFind.step`), `StringLoops`, `HardCoreLoops`, `ThreeColoring/Machines`); controls fail sealed and pass unsealed as designed. Limits: explicit `simp [d]`/`unfold d` covered by a syntactic scan (0 hits in scope); `hostTM`/`copyTM` cannot be sealed (their configuration types read `.k`/`.State`), value-level reads go through `hostTM_k`, `hostTM_tm_q₀`, `copyTM_k`; `ModuleHost.State` and `IterateFind.hostTM` are notation (with `state_eq`, `hostTM_eq`).
5. Lint after (`lint-after.log`): check 8/8b lists empty for the six Build files and `ModuleHost.lean`; only change vs base is the five WARNs gone. Pre-existing: `SAT.lean` (over 1000 lines, now 4070; six missing sketches), `ThreeColoring/Machines.lean` (docstrings, sketches), check 8 on `Closure.layout`, `Repetition.guardedStep`, `HardCoreLoops.bound`/`input`, facade "does not import child" FAILs for `Build/Contract/*` and `EmitIter*`.
6. Statement diff (`statements.md`): 8 declarations moved to the host, 17 renamed (item C), 5 statements changed (the `HostState`/`hostEntry` renames inside IterateFind's host lemmas), 1 made public (`stateFind`), 53 added (plus `simps` lemmas). No other public statement changed.

## Open questions (worker)

1. Five pre-existing `| zero => rfl` reads of `StateLoop.orbit` (`EncodingMachines.lean:572`, `GI/Efficiency.lean:141`, `GI/EfficiencyRep.lean:194, 388`, `GGMReductionEval.lean:534`), outside scope: fix in part 2.
2. `Build/Loop.lean` keeps a private `loop_first_halt` equal to `ModuleHost.first_halt` (upstream of the host): move `first_halt`/`live_prefix` down later?
3. `ModuleHost.clean_install`/`clean_emit` destructure `PolyTimeComputable` by `obtain` (no `_iff`); `exists_compParam`/`exists_comp` read `runAtL`/`advInput` by `simp` (outside this seal).
4. The duplication ledger is on the records branch; not updated here.
5. `ModuleHost.lean` imports `ClassNP.PolyTime` (as `IterateFindHost` did).
