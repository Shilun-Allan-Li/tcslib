<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xDistance_sq_disjointSpecialYFalse_le_gamma_pow_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared distance bound

**Claim.** Under the stated information bound, the expected squared total variation distance from uniform, conditioned on Bob’s special bit being false, is at most $\gamma^4$.

**Proof.** By the fiberwise Pinsker inequality (`two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse`), twice the expected squared distance is at most the expected fiber KL divergence. The information bound implies that this KL expectation is at most $2\gamma^4$. Combining the inequalities gives twice the desired expectation at most $2\gamma^4$, and division by two proves the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.integral_xFiberKL_disjointSpecialYFalse_le_two_mul_gamma_pow_four`.
