# Gate 108 (#217, NZ-1 dedup): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256
`4bb3783081b43f91e9a2567b9c7eae8b80f92f5e16dce9537be71c94f05bf268`). **Verdict: PASS WITH MINORS:
0 blockers, 0 majors, 2 minors, 6 notes. The gate is CLOSED.** The merged-tree replay after #216
remains a condition of the merge (note 8).

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Fixed in #217** (the standing rule, WORKFLOW §3). `ExpectedTime`'s `notHaltedProb_haltRun_zero` now closes its inner nonhalting step with `NDTM.not_haltsWithin_zero`: a halted empty-word run would give `HaltsWithin x 0`, through `haltsWithin_iff` and `List.length_eq_zero_iff`. The probability wrapper is kept. The NZ-1 census is now 8 sites (6 nondeterministic, in 5 files, two of them in `ExpectedTime`; 2 deterministic), and the ledger's search adds probability and expected-time formulations and `simp` closures without `at` (note 6). Evidence: the freeze and the replay at the new head. |
| 2 | minor | **Accepted.** The pack's lint line was wrong about where the 45 policy findings come from: 28 are in `ExhaustiveReplay`, 1 in `NDNormalForm` and 16 in `Loop`. `Loop`'s include missing module headings and two parser false positives, `lemma modeled` and `lemma lemma.`, inside `exists_emitLoopTM`'s docstring. The counts were right. This is recorded here, and no repair is needed in this PR. |
| 3–8 | note | No change. Note 8's condition is carried into the merge order (HANDOFF). |
