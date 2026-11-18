# Efficiency remediation: rulings on audit r1 (Seyoon, 2026-11-18)

Audit: `audit-r1.md` (records, this folder). Standing rule 15 (`briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2).

| Q | Ruling |
|---|---|
| Q1 | (A) Efficiency in the named primitive predicate (`StrongOneWay.easy`, `PRG.Secure`, `InteractiveProof`/`ZK`, `HBCSecure`, …) satisfies rule 15: the raw structure is the allowed raw bundle, the primitive cannot hold without the proof ([PS10] Defs 27.3, 77.1). |
| Q2 | (A) #377 lands as audited; EF-R1 proves `ReductionEfficient`/`LeveledReductionEfficient` for every family (TM tooling, parameters as advice); A1/A3 become unconditional by one-line wrappers; P6-Q10 superseded. |
| Q3 | (A) `EfficientFamily extends Family` (uniform parameter map, noise sampler in the #378 contract form); `DLWEAssumption`/`SISAssumption` stay on the raw `Family`; every scheme instance requires `EfficientFamily`. |
| Q4 | (A) Rule 15 supersedes pairing Q5: `BilinearGen` carries `Ops` (EF-D2); `IBEScheme` gains uniform machine fields (EF-D3); BB1 re-inhabited (EF-H10) with statistical draws and a correctness-preserving fallback. |
| Q5 | (A) Discharge 8 `ArithmeticFP` fields incl. `xgcd` (EF-H1); split the bundle so only `PrimesInP` (true by AKS) remains a named hypothesis; factoring/RSA/Rabin generators conditional on it, a recorded standing exception. |
| Q6 | (A) `SafePrimeGen`, `FullGroupGen`, `BilinearGen` are assumption objects ([PS10] pp. 52–53), documented as such. |
| Q7 | **(B) Retrofit secret sharing and BGW now (EF-H11)**, not exempt. |
| Q8 | **Prove it now.** Seyoon: "there must be a proof that 3-colouring is NP-hard somewhere in the complexity literature. if not, yes, now is a good time to add that in." TCSlib has the graph-level 3SAT → 3COL equivalence (`Complexity/NPReductions/ThreeSATToColoring.lean`, `SATtoColorReduction`, course material) and Cook–Levin (`Complexity/CookLevin`), but not the string-level Levin reduction with polynomial-time instance and witness maps that `LevinNPHard L3COL R3COL` needs (`ZeroKnowledge/NP.lean:654`). EF-H12 builds it, reusing those read-only; standard sources: Cook–Levin with witness maps [AB09 §2.3, Thm 2.10 and the Levin-reduction remark], 3SAT → 3COL (e.g. [Gar–Johnson 1979]/[AB09 Exercise 2.x]); citations to be pinned in the brief. Arora–Barak material is read-only. |
| Q9 | (A) Define `LossyTDF`/`ABOTDF` interfaces now (EF-D4), efficiency in the definition. |
| Q10 | (A) Route everything feasible on TM tooling now (all but GSW Eval); RAM-routed items allowed only with the admission disclosed, counted as proved only once `WordRAM.exists_simulation` is proved. |
| Q11 | (A) Start the file-disjoint jobs now (EF-H1, EF-R2/R3, EF-D4, EF-D1, then EF-H4; plus EF-H11 and EF-H12 per Q7/Q8 if file-disjoint from Stage 2); hold the Candidates, Pairing and IBE retrofits (EF-H2, EF-D2, EF-D3, EF-H10, EF-R6) until S2-A and J4 merge; EF-R1 after #377 merges; non-dyadic halves after #378 merges; EF-H8 (GSW Eval) after the RAM bridge. |
