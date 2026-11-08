<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fiber KL decomposition using conditioned laws

**Claim.** The expected fiberwise KL divergence equals the sum over statistic values of the fiber measure times the KL divergence of Alice’s special-bit law conditioned on that fiber, relative to uniform.

**Proof.** First decompose the expectation as a finite sum of fiber measures multiplied by the fiberwise KL divergences (`integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable`). For each statistic value, a zero-measure fiber contributes zero to the weighted sum. On every nonzero-measure fiber, the fiberwise KL divergence agrees with the KL divergence computed from the disjoint-and-special-bit-false distribution conditioned on that fiber (`xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero`). Replacing each summand accordingly yields the stated decomposition.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero`.
