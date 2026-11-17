<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedModelCostSum_le_of_first_eq_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Bound for a Negative First Sign

**Claim.** For every nine-coordinate sign vector whose coordinate indexed by $0$ is $-1$, the sum of the interleaved model costs over all depth-two seeds is at most $571$.

**Proof.** The proof checks this finite assertion by exhaustive computation: the sign vector has finitely many possible coordinates, and the seed set is finite, so the sum is a finite sum of explicitly defined costs. Evaluating these definitions under the assumption that coordinate $0$ is $-1$ verifies the stated upper bound in every case.
