# Gate 105 (#214, AS-1 dedup): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256
`258b3096276701245123f51c7ed39e53f466d475f42beb55b560f1c01abad327`). **Verdict: HOLD: 0 blockers,
1 major, 0 minors, 4 notes.** The targeted rewrite of `astep_call₁` passes (note 2).

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Fixing in #214, all of it** (the user, 2026-11-06: "All 130 in #214"). A by-kind scope (`campaign/items/dedup/as1-SCOPE.md`) searched every closing form outside `Machines/ARM`: the `simp`/`simpa` family with `astep`, the `regs [astep, …]` macros, and PathHard's `stp` macro. It found **181 containing declarations in 40 files**. 8 are excluded as machine comparisons (`astep_cases`, `arm_step`, `arm_run`, `mstep_det`, `mrun_eq_arun`, `astep_mdetPart`, `nastep_det`, `PSem.of_areach`), with their literal one-step branches re-pointed where the edit is local. That leaves 173 in scope. Already on #214 (`1fd7d4ce`, `1856e771`, `5fdcfcf4`, `090fcccd`, `29c41e09`): the five circuit equations (now allowed: the user's 2026-11-06 ruling on colleague files), the auditor's four `TQBFARM` continuations (`rw [astep_call hl, vword_whole₁]`), `UnaryLogspace`'s `LtM.loop` and `ltLang_mem` (note 3), NARMKit's 17 and NARMPSem's 14 step lemmas, `AHalt.ret`/`MHalt.ret`, and four `QueryReshape`/`Mult` lemmas. The remaining 130 are in progress on the same branch. Round 2 audits the whole family on a fresh merged-tree replay. The ledger's AS-1 census is to be rewritten from the scope at round 2. |
| 2 | note | No change. |
| 3 | note | Included in finding 1 (`5fdcfcf4`). |
| 4 | note | **Superseded:** the five circuit members are re-proved through the general equations (`1fd7d4ce`), now that the user's ruling on colleague files allows it. |
| 5 | note | No change. |

## Round 2 findings (received 2026-11-06)

`findings-r2.md`, verbatim (SHA-256
`bce67db29cfcb29d32b77870324fa6458874fd237dd1c4b48a0ac118660b55a0`). **Verdict: HOLD: 0 blockers,
2 majors, 2 minors, 3 notes.** The freeze, the explicit replacements, the macro change and the
exclusions are verified (notes 5–7).

**The user's ruling (2026-11-06):** land #214 as it is, a strict improvement over the base, and
**acknowledge both majors as scoped debt with scheduled resolutions**, separate PRs in this dedup
window.

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Acknowledged (the user, 2026-11-06), ledger family AS-2.** These are implicit `astep` reductions by unification, with no `astep` in the text: `AReach.step`/`AHalt.step` followed by `change`/`exact` on a concrete continuation. The members named so far are `Mult`'s `mult_row_start`, `mult_contribution`, `mult_inner_loop`, `mult_outer_loop`, `mult_next_column`, `mult_columns_run` and `mult_last_bit`, and `QueryReshape`'s `comp_factor_run`, `comp_valid_inner`, `comp_multiply` and `comp_separator_run`. **Resolution:** a census by an `astep` irreducibility seal over every consumer, with controls, then a re-pointing PR, after #214 merges. `Mult`'s one-fifth crossing is part of the acknowledgment. |
| 2 | major | **Acknowledged (the user, 2026-11-06), ledger family MT-1, the machine-table equations.** Consumers read each machine's instruction table (`A`, `CA`, …, defined in `TQBFARM/Machine`, `PathHardMachine`, `Codec/Machine`, the SavitchARM, ExpBFS and circuit machine files) by `show A .l = _ from rfl` or `simp [A]`. That read predates AS-1: the old proofs did `simp [astep, A]`. #214 makes it visible; it does not create it. `NARMExample`'s `guessValidA` reduces `NARM.detPart` and should use `NARM.detPart_det`. **Resolution:** publish per-label instruction equations (`A_<label>`) in each machine's own file and re-point the consumers, a separate PR per machine directory in this window. Colleague files are mechanical, with an FYI. Round 2's pack wrongly said these readings stay within each machine's file. That claim is withdrawn. |
| 3 | minor | **Accepted.** The scope table counts unfolding occurrences per site at the base: 583 sites, 47 of them in the eight exclusions, so 536 in scope. The implementation report counts edited sites: 501, of which 18 are caveat sites. The two conventions differ because one edit can retire several occurrences on a line. The pack's 501 is the edit count. `PSem.of_areach`'s `Function.iterate_fixed rfl` (lines 343, 362, 380) does compute `astep` at a halted configuration. It is inside a recorded exclusion and is recorded under AS-2 (`arun_halted` gives the run fact). |
| 4 | minor | **Accepted; the attestation is narrowed.** The retained per-file logs cover 35 of the 38 files. `ARMProof`, `NARMKit` and `UnaryLogspace` are covered only by the 109-module replay, which elaborates all 38. The `stp` negative control's log was not retained, so that sentence is withdrawn. |
| 5–7 | note | No change. |

**Round 3** checks these dispositions and the ledger's AS-2 and MT-1 entries, with no change to
#214's code.
