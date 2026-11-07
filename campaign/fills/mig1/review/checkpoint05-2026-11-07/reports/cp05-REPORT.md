# MIG-1 megafill — checkpoint cp05 (F-B targets complete) — PARTIAL

Agent: Claude (Anthropic). Branch `fill/mig1-mega` from exactly
`83ac315ed9e7089466bd16a32f3b71fbadc556d2`; records `7df0d047d501a1d08982d17d20208faf49d39131`.
Commits: `COMMITS.txt` (F-A ×2, F-C, F-B). Verdict: **partial (checkpoint)**.

## F-B results (axioms standard — `axioms/Ax_fb.*`, 17 names)
- `polyUnaryTM_spaceUsed`: proved, with the head invariant moved from Catalog
  (`f2_polyHeads`, `f2_polyHeads_bounds`, `f2_poly_step`, `f2_poly_space` → Primitives
  `polyHeads`, `polyHeads_bounds`, `poly_step`, `poly_space`); `f2_head_steps` replaced by
  `MultiTapeTM.workTapePos_runFrom_mem_Icc`, the interval count by `spaceUsedByTape_le_card_Icc`.
- `unaryTokenTM_computes`, `appendBitTM_computes`: proved from the rows' bodies, cleaned with
  `initCfg_eq`/`Cfg.init_*`, `step_of_some`, `Action.apply_*`; `computesFunInTime_unaryToken`,
  `computesFunInTime_appendBit` are corollaries.
- **Forwarding exports (the three gated additions):** `Turing.FinTM.pairMapSndTM`,
  `pairMapSndTM_computes` (coefficient 22), `pairMapSndTM_spaceUsed` (coefficient one on `Sg`).
  Headers identical to `inputs/forwarding-map-contract.lean.txt`, definition body identical
  (`forwarding-contract-check.log`). Witness: Catalog's forwarding controller `a2_mapTM Mg true`,
  moved with its private implementation (renamed `fwdMap*`: `FwdMapState`, `fwdMapAct`,
  `fwdMapTM`, `fwdMapCfg`, `fwdMapVirtual`, … `fwdMap_space`, per the gate's fate table); its
  transition table is unchanged modulo renaming. Catalog's `a2_mapSumEquiv`/`a2_map_sum` are not
  moved (replaced by `Fin.sum_univ_add`). Both theorem proofs are complete.
- `computesFunInTime_pairMapSnd` re-pointed to `pairMapSndTM` (c = 22). The old captured-output
  mapper (`mapAction`, `pairMapTM`, `mapCfg`, … `pairMap_computes`) and the then-unreachable
  `catalogPayload_computes` are retired from Primitives.
- `computesFunInTime_pairDup` uses `Turing.pairDiagTM` (c = 5); private `pairDupTM`,
  `pairDup_double`, `pairDup_computes` retired.
- The existing Primitives specs that depended on F-A/F-C (`polyBitsTM_computes`,
  `pairLenCheckTM_computes`, `stripLastTM_computes`, `splitSolveTM_computes`,
  `splitSolveTM_spaceUsed`, `splitSolveWithTM_computes`) now print only standard axioms.

## Checks (fresh)
`elab/fb*.summary` (Primitives exit 0, 0 sorry); `tail-fb/summary.log` (35 downstream bootstrap
modules, failed=0); `freeze-cp05.log` (PASS: exactly the three authorized additions, no removal);
`static-sorry-cp05.log` (TOTAL 3 = the frozen RAM admissions only).

## Seal status for Primitives — INCOMPLETE at cp05
`seal/Seal_Primitives.out`: sealing all 42 changed/new Primitives declarations gives 18 errors,
all inside **verbatim-moved** material (`fwdMap_*` lemmas and `poly_space`): definitional reads
of `runFrom 0`, `runFrom 2 = step (step _)`, `initCfg` fields, `Action.apply` output and
`controlAction` (the same reads the Catalog originals made). New public statements' proofs
(`pairMapSndTM_*`, the three specs) are not among the failures. The argument scan also shows the
moved `poly_step` passes `MultiTapeTM.step`/`Action.apply` to `simp` explicitly. These moved
proofs need rewriting through the published equations; listed as remaining work.

## Remaining
F-D (Catalog retirements, consumers, WordSize docs), the Primitives seal repairs above, MIG-24
T2/T2b/T3 dispositions, compiled census, screens, 641-module sweep.
