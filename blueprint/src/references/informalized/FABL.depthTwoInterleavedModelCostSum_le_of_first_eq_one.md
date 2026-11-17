<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedModelCostSum_le_of_first_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Bound for a Positive First Sign

**Claim.** For every nine-coordinate sign vector whose coordinate indexed by $0$ is $1$, the sum of the interleaved model costs over all depth-two seeds is at most $571$.

**Proof.** The proof checks this finite assertion by exhaustive computation: there are finitely many sign vectors and finitely many depth-two seeds, and each cost is explicitly defined. Evaluating the finite sum subject to coordinate $0$ being $1$ verifies the bound in every case.
