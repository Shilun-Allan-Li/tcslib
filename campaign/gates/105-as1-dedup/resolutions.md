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
