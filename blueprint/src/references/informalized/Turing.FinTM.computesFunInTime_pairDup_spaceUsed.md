<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairDup_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair duplication with constant space

**Claim.** There are a finite Boolean Turing machine and a constant, chosen as $4$, that compute the pair encoding $(x,x)$ in at most $4(|x|+1)$ steps on every Boolean word $x$, while using at most $4$ work-tape cells at every time.

**Proof.** Choose the pair-duplication machine, which has zero work tapes. Its computation produces the required pair encoding within $4(|x|+1)$ steps (`f2_pairDup_computes`). Since there are no work tapes, total space used is zero at every time (`spaceUsed_zero_tapes_eq_zero`), hence in particular at most $4$.

**Key facts.** `Turing.FinTM.f2_pairDup_computes`, `Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`.
