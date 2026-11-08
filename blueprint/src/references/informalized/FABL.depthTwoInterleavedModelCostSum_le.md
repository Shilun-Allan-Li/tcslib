<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedModelCostSum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Interleaved Model Cost Bound

**Claim.** For every nine-coordinate sign vector, the sum of the interleaved model costs over all depth-two seeds is at most $571$.

**Proof.** The first coordinate of a sign vector is either $1$ or $-1$. In the first case, apply the bound for vectors whose first sign is positive (`depthTwoInterleavedModelCostSum_le_of_first_eq_one`); in the second, apply the bound for vectors whose first sign is negative (`depthTwoInterleavedModelCostSum_le_of_first_eq_neg_one`). These cases exhaust the possible signs, giving the claimed bound for every vector.

**Key facts.** `FABL.depthTwoInterleavedModelCostSum_le_of_first_eq_one`, `FABL.depthTwoInterleavedModelCostSum_le_of_first_eq_neg_one`.
