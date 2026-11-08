<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.one_half_le_uniformProbability_mulVec_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero matrix image probability

**Claim.** For a nonzero matrix $D$ over $\mathbb F_2$, a uniform vector $x$ satisfies $Dx\ne0$ with probability at least $1/2$.

**Proof.** Use the matrix-product verification bound with proposed product zero: since $D\ne0$, this proposed product is incorrect, so the probability that the verifier accepts is at most $1/2$ (`uniformMatrixProductVerificationAcceptanceProbability_le_half`). For this choice, acceptance is exactly the event $Dx=0$; the verification predicate characterization identifies it with that kernel event (`matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero`). The events $Dx=0$ and $Dx\ne0$ are complementary, and their uniform probabilities sum to one. Therefore the latter probability is at least $1/2$.

**Key facts.** `FABL.uniformMatrixProductVerificationAcceptanceProbability_le_half`, `FABL.matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero`.
