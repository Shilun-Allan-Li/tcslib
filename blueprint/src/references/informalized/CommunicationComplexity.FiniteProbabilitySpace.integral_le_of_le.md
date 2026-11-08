<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.integral_le_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise bounds pass to the integral

**Claim.** If a function on a finite probability space is everywhere at most a constant, then its integral is at most that constant.

**Proof.** Write the integral as the finite sum of function values weighted by the real PMF masses. Each weight is nonnegative, so multiplying the pointwise bound by that weight preserves the inequality. Summing gives an upper bound by the constant times the sum of all weights. Those weights sum to one, so the resulting bound is the constant.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.integral_eq_pmf_sum`, `CommunicationComplexity.FiniteProbabilitySpace.pmf_toReal_nonneg`, `CommunicationComplexity.FiniteProbabilitySpace.pmf_toReal_sum_eq_one`.
