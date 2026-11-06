> **Historical** (gate 105 round 3, minor 1): this table describes the base `1fd7d4ce`, counting one
> site per unfolding call. The census of record is 583 sites, 47 excluded, 536 in scope. #214 re-points
> every in-scope declaration; the implementation agent's "501 sites" count is withdrawn.

# AS-1 widened scope: proofs that unfold `astep` to compute one instruction step

Base `1fd7d4ce` (branch `lean/dedup-as1`). Scan of every `.lean` file under `TCSlib/` except
`SpaceComplexity/Machines/ARM.lean` (the equations' home), by containing declaration.

**Forms searched.** `simp`/`simp only`/`simpa`/`simpa only`/`simp_all`/`dsimp`/`simp_rw`/`norm_num`/`aesop`
with `astep` (bare or namespace-qualified, not `astep_*`, not `nastep`/`mstep`) in the lemma list, the
scoped `regs [astep, …]` macros (TQBFARM, SavitchARM, ExpBFS, PathHard: they expand to `simp only`),
the PathHard `stp` macro (its body is `simp only [astep, A, …]`), `unfold`/`delta astep`,
`rw`/`rewrite`/`erw [astep]`, and `show`/`change` lines naming `astep`. Found: only the simp-family,
`regs` and `stp` forms. No `unfold astep`, `delta`, `dsimp [astep]` or `rw [astep]` exists; the two
`show`/`rw` hits (`mrun_eq_arun`, `PSem.of_areach`) state `astep` of an iterate, they do not unfold it.
Sites that compute a step by `rfl`/defeq without naming `astep` are not counted.

**General equations** (`SpaceComplexity/Machines/ARM.lean`, section `Steps`, all with hypothesis
`h : A l = .<ins>` at a live configuration `(some l, v, res)`): `astep_inc`, `astep_dec`, `astep_clr`,
`astep_half`, `astep_jz`, `astep_jodd`, `astep_jeq`, `astep_call`, `astep_ret`, `astep_valP`,
`astep_valQ`, `astep_jeqIn`, `astep_jeqFst`, `astep_jeqSnd` (14). Derived, already through them:
`LogProg.astep_call₁` (UnaryLogspace, `unaryFst`), `BoolCircuit.AdjScan.astep_rd`/`astep_hit`/
`astep_jeqFst`, `BoolCircuit.AdjWalk.astep_call₁`/`astep_call₂`. Call sites also need the `vword_*`
lemmas (`vword_whole₁/₂/₃`, `vword_unary₁/₂`). For NARM/MARM deterministic instructions the step
is `astep (fun _ => i)`, re-pointed with `(A := fun _ => i) rfl`.

**Instruction kinds** in the per-declaration table: exact for the changed rows; for the rest, a
heuristic from the declaration's instruction hypotheses, `vword_*` uses and the labels it names
looked up in its directory's machine tables (may include kinds of labels named but not stepped;
`—` = labels passed by hypothesis or `step_of rfl`, kind per site).

## Totals

- Containing declarations found: **181** in 40 files (583 unfolding sites).
- Excluded (machine comparisons): **8**. In scope (step computations): **173**.
- Re-pointed in this change: **43**. Remaining: **130** (over the ~60 threshold, so Step 2 took the reduced path).

## Per file

| File | containing / total decls | excluded | in scope | changed | remaining |
|---|---|---|---|---|---|
| `CircuitComplexity/LogspaceUniformAdj.lean` | 2 / 16 | 0 | 2 | 0 | 2 |
| `CircuitComplexity/LogspaceUniformExample.lean` | 2 / 11 | 0 | 2 | 0 | 2 |
| `CircuitComplexity/LogspaceUniformScan.lean` | 7 / 39 | 0 | 7 | 0 | 7 |
| `CircuitComplexity/LogspaceUniformWalk.lean` | 7 / 43 | 0 | 7 | 0 | 7 |
| `ClassPSPACE/TQBFARM/Correct.lean` | 2 / 4 | 0 | 2 | 0 | 2 |
| `ClassPSPACE/TQBFARM/Leaf.lean` | 6 / 8 | 0 | 6 | 2 | 4 |
| `ClassPSPACE/TQBFARM/Walk.lean` | 7 / 14 | 0 | 7 | 2 | 5 |
| `Randomized/SpaceAmplifyPolyRun.lean` | 2 / 14 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/Codec/Deciders.lean` | 1 / 22 | 0 | 1 | 0 | 1 |
| `SpaceComplexity/Codec/Engine.lean` | 3 / 6 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/Codec/Layout.lean` | 3 / 8 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/Codec/Layout2.lean` | 2 / 5 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/Codec/StepDecider.lean` | 3 / 8 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/CounterProgSim.lean` | 3 / 25 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/CounterProgSimRun.lean` | 1 / 6 | 0 | 1 | 0 | 1 |
| `SpaceComplexity/ExpBFS/Main.lean` | 2 / 24 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/ExpBFS/Relax.lean` | 3 / 24 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/ExpBFS/Run.lean` | 5 / 40 | 0 | 5 | 0 | 5 |
| `SpaceComplexity/ExpBFS/Search.lean` | 3 / 6 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/Logspace/InputAccess.lean` | 8 / 81 | 0 | 8 | 0 | 8 |
| `SpaceComplexity/Logspace/Mult.lean` | 12 / 62 | 0 | 12 | 1 | 11 |
| `SpaceComplexity/Logspace/PathHardRun.lean` | 1 / 4 | 0 | 1 | 0 | 1 |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | 4 / 14 | 0 | 4 | 0 | 4 |
| `SpaceComplexity/Logspace/QueryReshape.lean` | 19 / 118 | 0 | 19 | 3 | 16 |
| `SpaceComplexity/Machines/ARMLoops.lean` | 6 / 11 | 0 | 6 | 0 | 6 |
| `SpaceComplexity/Machines/ARMProof.lean` | 1 / 25 | 0 | 1 | 1 | 0 |
| `SpaceComplexity/Machines/ARMReach.lean` | 2 / 5 | 2 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/ARMRun.lean` | 1 / 9 | 1 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | 5 / 20 | 0 | 5 | 0 | 5 |
| `SpaceComplexity/Machines/MARM.lean` | 3 / 27 | 2 | 1 | 1 | 0 |
| `SpaceComplexity/Machines/MARMCompile.lean` | 1 / 27 | 1 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/NARM.lean` | 1 / 36 | 1 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/NARMExample.lean` | 2 / 5 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/Machines/NARMKit.lean` | 17 / 32 | 0 | 17 | 17 | 0 |
| `SpaceComplexity/Machines/NARMPSem.lean` | 17 / 30 | 1 | 16 | 14 | 2 |
| `SpaceComplexity/SavitchARM/Recursion.lean` | 8 / 17 | 0 | 8 | 0 | 8 |
| `SpaceComplexity/SavitchARM/Run.lean` | 2 / 19 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/SavitchARM/Search.lean` | 2 / 18 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/SavitchARM/Setup.lean` | 3 / 5 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/UnaryLogspace.lean` | 2 / 25 | 0 | 2 | 2 | 0 |

(total decls = `theorem`/`lemma`/`def`/`abbrev`/`instance`/`example` in the file.)

## Excluded (not step computations)

| File | Declaration | Why excluded |
|---|---|---|
| `SpaceComplexity/Machines/ARMReach.lean` | `astep_cases` (L53) | statement is about `astep` at an arbitrary label (shape of every step); the case split is over all instruction kinds, no one instruction is computed for a machine |
| `SpaceComplexity/Machines/ARMReach.lean` | `arm_step` (L90) | compiled-machine simulation (ARM vs `armProg`): inverts an abstract step hypothesis `hs` per instruction case to feed the `sim_*` lemmas; compares two machines |
| `SpaceComplexity/Machines/ARMRun.lean` | `arm_run` (L119) | compiled-machine simulation (ARM vs `armProg`), the run analogue of `arm_step`; per-case `simp [astep, hA]` side goals sit inside a machine comparison (each branch would accept `astep_<kind> hA`; listed here for the record, not re-pointed) |
| `SpaceComplexity/Machines/MARM.lean` | `mstep_det` (L146) | compares `mstep` with `astep (A.detPart β)` at a register label (machine comparison, MARM vs its deterministic part) |
| `SpaceComplexity/Machines/MARM.lean` | `mrun_eq_arun` (L251) | transfer of whole runs MARM vs deterministic part; the one inner `simp [astep, hret]` is the detPart answer at a memory label inside the comparison (would accept `astep_ret hret`) |
| `SpaceComplexity/Machines/MARMCompile.lean` | `astep_mdetPart` (L265) | compares the deterministic parts `A.detPart β` and `A.detPart β'` (machine comparison) |
| `SpaceComplexity/Machines/NARM.lean` | `nastep_det` (L130) | compares `nastep` with `astep (A.detPart β)` (machine comparison, NARM vs its deterministic part) |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.of_areach` (L328) | transfer of runs ARM-detPart vs PSem semantics; the `show`/`rw` hits state `astep` of the iterate (no unfold), the inner `simp [astep, NARM.detPart_choose hA]` is the detPart answer at a `choose` label inside the comparison |

## Per declaration

| File | Declaration | sites | instruction kinds | equation(s) | status |
|---|---|---|---|---|---|
| `CircuitComplexity/LogspaceUniformAdj.lean` | `lang_mem` (L118) | 2 | valP | `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformAdj.lean` | `walk_lang` (L264) | 2 | ret, valP | `astep_ret`, `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformExample.lean` | `loop` (L97) | 2 | call, inc, jeqIn, ret | `astep_call`, `astep_inc`, `astep_jeqIn`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformExample.lean` | `leLang_mem` (L161) | 2 | call, valP | `astep_call`, `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `uloop` (L279) | 2 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `argsSkip` (L319) | 4 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `argsEx` (L369) | 3 | inc, jeqFst, jeqSnd, valQ | `astep_inc`, `astep_jeqFst`, `astep_jeqSnd`, `astep_valQ` | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `gateSkip` (L424) | 4 | inc | `astep_inc` | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `hitGate` (L460) | 5 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `nloop` (L564) | 3 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `scan_halts` (L628) | 1 | valP | `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `Em.emit` (L253) | 2 | inc, jeqIn, ret | `astep_inc`, `astep_jeqIn`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `uLoop` (L342) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `aLoop` (L380) | 6 | call, jeq | `astep_call`, `astep_jeq` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `gLoop` (L511) | 1 | call, clr, ret | `astep_call`, `astep_clr`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `inLoop` (L585) | 1 | call | `astep_call` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `oLoop` (L618) | 3 | jeq, ret | `astep_jeq`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `walk_halts` (L655) | 3 | call, ret, valP | `astep_call`, `astep_ret`, `astep_valP` | remaining |
| `ClassPSPACE/TQBFARM/Correct.lean` | `inner_spec` (L67) | 5 | call, clr, dec, jz | `astep_call`, `astep_clr`, `astep_dec`, `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Correct.lean` | `truth_mem_PSPACE` (L181) | 3 | inc, jz | `astep_inc`, `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `read_t` (L56) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `read_f` (L66) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `lc_run` (L101) | 4 | call | `astep_call` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `lv_run` (L146) | 6 | call | `astep_call` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `lit_run` (L206) | 2 | call, inc | `astep_call`, `astep_inc` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `formula_run` (L282) | 4 | call, jz | `astep_call`, `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `len_t` (L57) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Walk.lean` | `len_f` (L67) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Walk.lean` | `syn_run` (L81) | 1 | call | `astep_call` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `node_run` (L138) | 1 | call, clr | `astep_call`, `astep_clr` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `push_run` (L158) | 4 | clr | `astep_clr` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `pop_run` (L186) | 5 | jz | `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `leaf_spec` (L238) | 2 | call | `astep_call` | remaining |
| `Randomized/SpaceAmplifyPolyRun.lean` | `ps_steps` (L113) | 1 | call | `astep_call` | remaining |
| `Randomized/SpaceAmplifyPolyRun.lean` | `ps_runs` (L354) | 1 | call | `astep_call` | remaining |
| `SpaceComplexity/Codec/Deciders.lean` | `init_tail` (L265) | 11 | call, clr, dec, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Codec/Engine.lean` | `scan_loop` (L97) | 4 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Engine.lean` | `halvCount_loop` (L244) | 4 | half, inc, jz | `astep_half`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/Engine.lean` | `le_loop` (L303) | 6 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Layout.lean` | `layout_run` (L92) | 7 | call, clr, half, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_half`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Codec/Layout.lean` | `le_phase` (L265) | 1 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Layout.lean` | `vscan_run` (L296) | 2 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Layout2.lean` | `layout2_run` (L67) | 6 | call, clr, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Codec/Layout2.lean` | `insym_run` (L219) | 11 | call, clr, dec, inc, jeq, jz | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/StepDecider.lean` | `pm_run` (L62) | 13 | dec, inc, jeq, jz | `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/StepDecider.lean` | `z_run` (L138) | 4 | dec, jz | `astep_dec`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/StepDecider.lean` | `step_tail` (L181) | 2 | jeq, jz, ret | `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/CounterProgSim.lean` | `pr_reach` (L260) | 5 | clr, inc, jeq, jeqIn | `astep_clr`, `astep_inc`, `astep_jeq`, `astep_jeqIn` | remaining |
| `SpaceComplexity/CounterProgSim.lean` | `pr_halt` (L303) | 6 | clr, inc, jeq, jeqIn, ret | `astep_clr`, `astep_inc`, `astep_jeq`, `astep_jeqIn`, `astep_ret` | remaining |
| `SpaceComplexity/CounterProgSim.lean` | `sim_step` (L355) | 11 | call, inc, jeqIn, ret | `astep_call`, `astep_inc`, `astep_jeqIn`, `astep_ret` | remaining |
| `SpaceComplexity/CounterProgSimRun.lean` | `UnaryLogspace.counterProg` (L142) | 3 | jeqIn, valP | `astep_jeqIn`, `astep_valP` | remaining |
| `SpaceComplexity/ExpBFS/Main.lean` | `fscan_run` (L127) | 4 | call | `astep_call` | remaining |
| `SpaceComplexity/ExpBFS/Main.lean` | `iter_run` (L270) | 1 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Relax.lean` | `ini_run` (L150) | 4 | call | `astep_call` | remaining |
| `SpaceComplexity/ExpBFS/Relax.lean` | `inner_run` (L229) | 7 | call | `astep_call` | remaining |
| `SpaceComplexity/ExpBFS/Relax.lean` | `outer_run` (L371) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `wo_run` (L242) | 4 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `wb_run` (L272) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `lg_run` (L396) | 4 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `setup_run` (L428) | 1 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `wk_run` (L493) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Search.lean` | `rounds_run` (L94) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Search.lean` | `count_run` (L166) | 5 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Search.lean` | `search_run` (L224) | 1 | inc, jz | `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `inputLength_loop` (L612) | 2 | call, inc | `astep_call`, `astep_inc` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `arm_chain` (L668) | 1 | — | per site | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `alignedPair_loop` (L728) | 6 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `registerCopy_loop` (L903) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `registerScale_loop` (L939) | 3 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `canonicalTail_loop` (L1023) | 7 | call, half, inc, jeq, jz | `astep_call`, `astep_half`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `boundedDecodeStride_loop` (L1125) | 6 | call, clr, dec, inc, jeq, jz | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `indexedSeek_loop` (L1294) | 6 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_contribution` (L602) | 3 | call, dec, inc, jeq | `astep_call`, `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_inner_loop` (L642) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_outer_loop` (L751) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_finish` (L858) | 2 | jeq, jz | `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_parity` (L871) | 4 | half, jodd | `astep_half`, `astep_jodd` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_result_read` (L895) | 2 | call, dec, jeq, jodd | `astep_call`, `astep_dec`, `astep_jeq`, `astep_jodd` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_next_column` (L916) | 2 | half, inc, jeq | `astep_half`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_columns_run` (L952) | 3 | clr, dec, jeq, jz | `astep_clr`, `astep_dec`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_last_bit` (L1081) | 4 | call, clr, dec, inc, jeq, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_canonical_run` (L1195) | 3 | dec, inc, jeq, jz | `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_sub_two` (L1270) | 2 | dec ×2 | `astep_dec code₀`, `astep_dec code₁` | changed |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_prepare_run` (L1291) | 1 | dec, half, inc, jeq | `astep_dec`, `astep_half`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/PathHardRun.lean` | `setup_run` (L110) | 7 | dec, half, inc, jeq, jz | `astep_dec`, `astep_half`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `dispatch_halt` (L109) | 30 | call, jz | `astep_call`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `tail_halt` (L175) | 3 | jz | `astep_jz` | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `matrix_halt` (L215) | 1 | — | per site | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `walk_halt` (L308) | 11 | — | per site | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_hit` (L421) | 1 | call (bit mode) | `astep_call (show dropARM false .hit = _ from rfl)` | changed |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_tail_decode` (L495) | 2 | call, clr, dec, inc, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_lookup` (L649) | 1 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_decrement_run` (L756) | 1 | dec | `astep_dec` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_z_prepare` (L777) | 1 | clr, dec, inc, jeq | `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_u_prepare` (L808) | 1 | clr, dec, inc, jeq | `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_lookup_prepare` (L842) | 1 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_product` (L1423) | 3 | clr, dec, inc, jeq, jz | `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_multiply` (L1498) | 2 | clr, inc, jeq, jz | `astep_clr`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_power_run` (L1583) | 2 | jeq, jz | `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_poly_run` (L1627) | 1 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_length_search` (L1677) | 5 | call, jeq, jz | `astep_call`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_canonical_run` (L1809) | 6 | call, clr, dec, inc, jeq, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_outer_prepare` (L1864) | 3 | dec, inc, jeq | `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_outer_decode` (L1933) | 3 | call, clr, dec, inc, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_inner_prepare` (L2045) | 3 | clr, half, inc, jeq | `astep_clr`, `astep_half`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_call_return` (L2117) | 1 | call | `rw [astep_call hc, vword_whole₁]` | changed |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_prefix_hit` (L2136) | 1 | half | `astep_half (show compARM C e false .prefixHit = _ from rfl)` | changed |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_separator_run` (L2207) | 6 | clr, inc, jeq | `astep_clr`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `move_run` (L115) | 4 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `move2_run` (L172) | 5 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `dmove_run` (L217) | 5 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `sub_run` (L257) | 4 | dec, jz | `astep_dec`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `halve_run` (L290) | 4 | dec, half, jz | `astep_dec`, `astep_half`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `shl_run` (L360) | 3 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMProof.lean` | `AHalt.ret` (L110) | 1 | ret | `astep_ret hA` | changed |
| `SpaceComplexity/Machines/ARMReach.lean` | `astep_cases` (L53) | 4 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/ARMReach.lean` | `arm_step` (L90) | 16 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/ARMRun.lean` | `arm_run` (L119) | 16 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `d1_loop` (L147) | 5 | jz | `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `d2_loop` (L174) | 4 | jz | `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `dbl_loop` (L200) | 3 | jeq, jz | `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `enum_loop` (L230) | 4 | call, jeq | `astep_call`, `astep_jeq` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `searchLang_mem_PSPACE` (L281) | 1 | call, inc, jz | `astep_call`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/MARM.lean` | `mstep_det` (L146) | 1 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/MARM.lean` | `MHalt.ret` (L218) | 2 | ret (det part) | `astep_ret (A := fun _ => .ret r) rfl` | changed |
| `SpaceComplexity/Machines/MARM.lean` | `mrun_eq_arun` (L251) | 3 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/MARMCompile.lean` | `astep_mdetPart` (L265) | 1 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/NARM.lean` | `nastep_det` (L130) | 1 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/NARMExample.lean` | `guessValidA_halts` (L57) | 4 | jz, ret, valP | `astep_jz`, `astep_ret`, `astep_valP` | remaining |
| `SpaceComplexity/Machines/NARMExample.lean` | `guessValidA_ans` (L75) | 4 | jz, ret, valP | `astep_jz`, `astep_ret`, `astep_valP` | remaining |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.inc` (L198) | 1 | inc (det part) | `astep_inc (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.clr` (L205) | 1 | clr (det part) | `astep_clr (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.half` (L211) | 1 | half (det part) | `astep_half (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jeq_pos` (L218) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jeq_neg` (L224) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jz_pos` (L230) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jz_neg` (L236) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jodd_pos` (L242) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jodd_neg` (L248) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.call_pos` (L254) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.call_neg` (L261) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_dec` (L268) | 1 | dec (det part) | `astep_dec (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₂_pos` (L275) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₂_neg` (L283) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₃_pos` (L291) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₃_neg` (L300) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.ret` (L309) | 1 | ret (det part) | `astep_ret (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.inc` (L136) | 1 | inc (det part) | `astep_inc (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.clr` (L143) | 1 | clr (det part) | `astep_clr (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.half` (L149) | 1 | half (det part) | `astep_half (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jeq_pos` (L156) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jeq_neg` (L162) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jz_pos` (L168) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jz_neg` (L174) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jodd_pos` (L180) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jodd_neg` (L186) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.call_pos` (L192) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.call_neg` (L199) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.ret` (L206) | 1 | ret (det part) | `astep_ret (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.of_areach` (L328) | 5 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/NARMPSem.lean` | `searchUp_run` (L389) | 1 | inc | `astep_inc` | remaining |
| `SpaceComplexity/Machines/NARMPSem.lean` | `searchDown_run` (L420) | 2 | dec | `astep_dec` | remaining |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.call` (L455) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.dec` (L463) | 1 | dec (det part) | `astep_dec (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `base_spec` (L149) | 3 | call, jeq, jz | `astep_call`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `desc1` (L199) | 6 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `desc2` (L272) | 6 | clr | `astep_clr` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `tail0F` (L335) | 2 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `tail1T` (L359) | 1 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `tail1F` (L379) | 2 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `loop_spec` (L426) | 1 | jeq | `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `call_spec` (L480) | 2 | — | per site | remaining |
| `SpaceComplexity/SavitchARM/Run.lean` | `mulL_run` (L169) | 3 | clr, jz | `astep_clr`, `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Run.lean` | `mul_run` (L201) | 1 | — | per site | remaining |
| `SpaceComplexity/SavitchARM/Search.lean` | `outerV_run` (L127) | 8 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Search.lean` | `outerU_run` (L207) | 4 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Setup.lean` | `ld_run` (L60) | 2 | jz | `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Setup.lean` | `pw_run` (L86) | 3 | jz | `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Setup.lean` | `setup_run` (L143) | 4 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/UnaryLogspace.lean` | `loop` (L221) | 5 | jeqIn (cmp, 2 sites), inc (i1, i2, i3) | `astep_jeqIn`, `astep_inc` via `show A .l = _ from rfl` | changed |
| `SpaceComplexity/UnaryLogspace.lean` | `ltLang_mem` (L277) | 3 | valP (start, 3 sites) | `astep_valP` via `show A .start = _ from rfl` | changed |

## Proposed split of the remainder (one PR per directory)

- `SpaceComplexity/Logspace`: 40 declarations, 157 sites (InputAccess.lean 8, Mult.lean 11, PathHardRun.lean 1, PathHardWalk.lean 4, QueryReshape.lean 16)
- `CircuitComplexity`: 18 declarations, 49 sites (LogspaceUniformAdj.lean 2, LogspaceUniformExample.lean 2, LogspaceUniformScan.lean 7, LogspaceUniformWalk.lean 7)
- `SpaceComplexity/Machines`: 15 declarations, 53 sites (ARMLoops.lean 6, ARMWidthExample.lean 5, NARMExample.lean 2, NARMPSem.lean 2)
- `SpaceComplexity/SavitchARM`: 15 declarations, 48 sites (Recursion.lean 8, Run.lean 2, Search.lean 2, Setup.lean 3)
- `SpaceComplexity/ExpBFS`: 13 declarations, 43 sites (Main.lean 2, Relax.lean 3, Run.lean 5, Search.lean 3)
- `SpaceComplexity/Codec`: 12 declarations, 71 sites (Deciders.lean 1, Engine.lean 3, Layout.lean 3, Layout2.lean 2, StepDecider.lean 3)
- `ClassPSPACE/TQBFARM`: 11 declarations, 37 sites (Correct.lean 2, Leaf.lean 4, Walk.lean 5)
- `SpaceComplexity`: 4 declarations, 25 sites (CounterProgSim.lean 3, CounterProgSimRun.lean 1)
- `Randomized`: 2 declarations, 2 sites (SpaceAmplifyPolyRun.lean 2)

The `SpaceComplexity/Machines` remainder is `ARMLoops` (6 generic loop runs, hypotheses `hA`),
`ARMWidthExample` (5), `NARMExample` (2) and `NARMPSem.searchUp_run`/`searchDown_run`; the
`Logspace` remainder includes the PathHard `stp` macro, whose body itself unfolds `astep`
(re-pointing its 5 using declarations means replacing the macro's `astep, A` by per-site equations).

## Landed on `lean/dedup-as1` (local, not pushed)

- `1856e771` TQBFARM: `read_t`, `read_f`, `len_t`, `len_f`.
- `5fdcfcf4` SpaceComplexity: `LtM.loop`, `ltLang_mem`.
- `090fcccd` Machines: `AHalt.ret`, `MHalt.ret`, 17 `NSem`/`nsem_*`, 14 `PSem.*`.
- `29c41e09` Logspace: `comp_call_return`, `drop_hit`, `comp_prefix_hit`, `mult_sub_two`.
