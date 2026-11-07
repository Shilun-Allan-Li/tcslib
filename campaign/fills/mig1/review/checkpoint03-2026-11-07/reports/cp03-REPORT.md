# MIG-1 megafill — checkpoint cp03 (F-C complete) — PARTIAL

Agent: Claude (Anthropic). Branch `fill/mig1-mega` from exactly
`83ac315ed9e7089466bd16a32f3b71fbadc556d2`; records `7df0d047d501a1d08982d17d20208faf49d39131`.
Commits: see `COMMITS.txt` (F-A 1/2, F-A 2/2, F-C). Verdict: **partial (checkpoint)**.

## Checkpoints reached
cp01, cp02 (F-A complete), **cp03 = F-C complete**. The time/configuration group and the
intrinsic space budget landed in one checked commit, so this zip serves as both the cp03 and cp04
recovery point; cp04 is not delivered separately (F-C's remaining MIG-24 items are listed below).

## F-C targets (all proved, axioms standard — `axioms/Ax_fc.*`)
`loopHostTM_contracts`, `loopHostTM_decides`, `loopHostTM_finds`,
`loopHostTM_spaceUsed_le_budget` (budget `23·k·(T |x| + 1)`, independent of `R |x|`),
`emitLoopTM_computes`; coefficient `10` preserved; first-visit cuts, positive round durations,
empty-output round configurations and both terminal values are the unchanged contract clauses.
Rows `exists_loopCfgTM`, `exists_loopTM`, `exists_loopFindTM`, `exists_emitLoopTM` are corollaries;
`callTM_run` unchanged (no `callTM_install`/`callTM_emit` added).

## Loop changes
- `loopHost_prepare`: fuel-head clause added (the gate's strengthened preparation), proved with
  `MultiTapeTM.workTapePos_runFrom_mem_Icc` and the `Cfg.init_*` equations.
- New private `loopCall_heads`; private `loopHost_contracts` restated with coefficient `10` and the
  two head clauses (the gate's extended contract), replacing its `∃ c` form.
- New private `segment_heads`, `seamed_space` (moved from Catalog `f2_segment_heads`,
  `f2_seamed_space`); Catalog's `f2_space_radius` is replaced by the published
  `MultiTapeTM.spaceUsed_le_of_abs_le` (no copy). Catalog sources are deleted in F-D.
- MIG-24 T1 (Loop part): private `loop_rewind_bounded` retired — call site uses the public
  `timed_rewind` (identical statement). `loop_first_halt` now derives from
  `MultiTapeTM.exists_first_halt`.
- MIG-24 T3 (`emCall_bank_initial`/`_final`): **not yet done** at cp03 (pending).
- MIG-24 T2 (`emCall_first_entry` ↔ Primitives `emitter_first_entry`): cross-file rename-mirror of
  two private lemmas; sharing needs a new public lemma, so recorded as a gap (no change).
- MIG-24 T7 (`loop_halted_run` ↔ `loop_run`): inspected; different terminals and bounds
  (already-halted `[false]` terminal with `N·B` versus an extra terminal segment with `(N+1)·B`);
  no change.

## Seal (fresh) — `evidence/seal/Seal_Loop.*`
All 15 changed/new Loop declarations sealed (core list + Simulation list): exit 0, 0 errors,
61 warnings = the base file's non-sorry warning multiset exactly. Earlier attempts retained
(`-try1` used a wrong list entry, `-try2`/`-try3` exposed `hF x` destructuring and an `initCfg`
input-position read, both replaced by `computesFunInTime_iff`/`computesInTime_iff` and
`initCfg_eq`/`Cfg.init_inputPos`). Argument scan `argscan/Loop.txt`: remaining foreign
arguments are `rightCfg` (in the base's `loopHost_prepare` capture step), `leftCfg` and
`captureCfg` (in `loopCall_heads`), plus `Cfg.Halted` (reducible abbrev); `words`/`cfg` hits are
local `let`s (false positives). **E1 extended:** `Turing.captureCfg` (Wrappers) also lacks field
equations (`captureCfg_workTapePos : (captureCfg emb ret pre out₀ c).workTapePos = fun i => if
h : i < k then c.workTapePos ⟨i, h⟩ else (pre ++ c.output).length`, and `_state`, `_workTapes`,
`_inputPos`, `_output`).

## Fresh checks in this zip (in addition to cp01/cp02)
`elab/fc*.summary` (Loop: exit 0, 0 errors, 0 sorry); `tail-fc/summary.log` (the 36 bootstrap
modules after Loop, at the F-C commit, failed=0); `axioms/Ax_fc.*` (10 names standard);
`freeze-cp03.log` (PASS); `static-sorry-cp03.log` (20 → 6: three Primitives targets and the three
frozen RAM admissions).

## Remaining exact obligations
F-B: `polyUnaryTM_spaceUsed`, `unaryTokenTM_computes`, `appendBitTM_computes`, the three
forwarding exports (`pairMapSndTM`, `_computes`, `_spaceUsed`), retirement of the captured-output
`pairMapTM` and the private `pairDupTM`. F-D: Catalog retirements and consumer re-points.

## NOT RUN at cp03
Compiled census, screens, 641-module sweep, policy lint.
