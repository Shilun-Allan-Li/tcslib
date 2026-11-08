<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fiber KL equals coarse information

**Claim.** The expected fiberwise KL divergence under the distribution conditioned on disjoint inputs and Bob’s special bit being false equals Alice’s conditional mutual information given the coarse data under that same distribution.

**Proof.** First identify the expectation of the fiberwise KL divergence with the conditional KL divergence of Alice’s special bit given the statistic made up of the transcript and the coarse data (`integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable`). The conditional KL divergence relative to the uniform bit law is exactly the conditional mutual information between that bit and the statistic (`condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable`). Finally, this mutual information is the coarse conditional information term in the statement (`mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse`). Chaining these equalities proves the result.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse`.
