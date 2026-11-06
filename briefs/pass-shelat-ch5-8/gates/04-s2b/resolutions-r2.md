# Gate 04 (S2b, #195): round 2 resolutions

- **Round 2:** findings `findings/gate04-s2b-r2-findings.md` on #195 at `243598b7`: **1 major (R2-01),
  2 minors (R2-02, R2-03)**. F01, F03, F04, F06, N1, N5, N6 fixed; F05 fixed for the accounting
  defect; N3 and N4 recorded; F02, N2 and N7 not resolved (F02 pending R2-01; N2 and N7 because the
  evidence was not in the bundle).
- **Repairs:** two commits on #195's branch after `243598b7`:
  - `81e4f4e21738e90eeef285a2a88fb7f664918a3a`: R2-01 (the seal extended to every consumer file;
    `Simulate.lean` and `PRF.lean` re-proved through published lemmas) and R2-03;
  - `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`: equation lemmas clearing check 8's three warnings.
- **Evidence** (`evidence-r3/`, **all in the bundle this time**): the replay, the axiom printout, lint,
  check 8, the seal script and its full output, the round 1 review, and the duplication ledger.

| Item | Severity | Resolution |
|---|---|---|
| R2-01 | major | **Fixed.** `QueryImpl.passthrough_apply` is proved by `rw [passthrough, ofComp_apply, OracleComp.call_bind]` (its own definition, a same-file lemma, a published lemma). The seal now covers **every consumer file of the change set, the new equation proofs included** (13 files, `seal-evidence.log`): all pass for the current version. To get there, pre-existing proofs were re-proved through published lemmas: in `Simulate.lean`, `simulate_bind`, `simulate_comp`, `simulate_withLog`, `simulate_costBoundedBy` and `simulate_call`; in `PRF.lean`, `acceptProb_random_eq_lazy`, `buildTree_boundedBy`, `toOracleAdversary_boundedBy` and `prfAdv_toOracleAdversary_zero`. New equation lemmas beside their definitions: `OracleAdversary.boundedBy_iff`, `lazyDist_apply`. The seal configuration's one non-definition entry (`abs_sub_le_sum_hybrids`) was removed. **Boundary, disclosed:** older ch. 2–4 proofs in `PRF.lean` (Frederick's, not S2b's) still read `distAdv`, `prfAdv`, `randomFunction`, `PRF` and the GGM reduction's helpers, which are not in the seal table. Gate 03d audits `PRF.lean` and the ch. 2–4 clean-up PR pays this back. |
| R2-02 | minor | **Fixed.** The bundle carries `evidence-r3/{replay.log, replay-order.txt, axioms.log, lint.log, check8.log, seal.py.txt, seal-evidence.log}`, the round 1 review (`review/gate04-review.md`, defining N1–N7) and the duplication ledger (rows DL-9 to DL-19 now exist; DL-9 includes `take_drop_ofFn_blocks`, gate 04 N4). |
| R2-03 | minor | **Fixed.** `InteractiveHandler`, `call` and `finish` (and their equation lemmas' docstrings): "a malformed move, or a further query after the budget is spent, gives the all-`false` result; a return at zero remaining budget is accepted". |
| F02 | major (round 1) | **Fixed with R2-01** (the seal is clean on every consumer file). |
| N2, N7 | minor | **Fixed:** check 8 is now 0 failures and **0 warnings** on `Games/` (the three S2a warnings cleared by `OracleSpec.add_dom_inl/_inr`, `add_rng_inl/_inr`, `sampleFin_eq`, `sample_eq`, `queryImpl_def`), and the seal output is attached. |
