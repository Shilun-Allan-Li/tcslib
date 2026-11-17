<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.quadraticInputConsistencyFunctionTester_seed_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic consistency seed bound

**Claim.** For every positive integer $d$, the seed space of the quadratic input consistency tester with parameter $d$ has cardinality at most $2^{3(d+1)^2}$.

**Proof.** The quadratic input consistency tester is obtained by padding and reindexing the affine consistency tester. These operations retain its seed space, so the two seed cardinalities agree. The affine tester's seed-cardinality bound is at most $2^{3(d+1)^2}$ (\texttt{affineConsistencyFunctionTester_seed_card_le}); applying it gives the claim.

**Key facts.** `FABL.affineConsistencyFunctionTester_seed_card_le`.
