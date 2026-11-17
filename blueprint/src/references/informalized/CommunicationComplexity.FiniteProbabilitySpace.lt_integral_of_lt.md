<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.lt_integral_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict lower bound for an integral

**Claim.** If a function is everywhere strictly greater than a constant on a finite probability space, then its integral is strictly greater than that constant.

**Proof.** Express the integral as the finite PMF-weighted sum. The weights are nonnegative, so the pointwise strict inequality gives a non-strict inequality after multiplying by each weight. Moreover, some point has strictly positive weight. At that point the weighted inequality is strict, so the sum of the weighted values is strictly greater than the sum of the weights times the constant. The weights sum to one, making that latter sum the constant. Hence the integral is strictly greater than it.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.integral_eq_pmf_sum`, `CommunicationComplexity.FiniteProbabilitySpace.exists_pmf_toReal_pos`, `CommunicationComplexity.FiniteProbabilitySpace.pmf_toReal_nonneg`, `CommunicationComplexity.FiniteProbabilitySpace.pmf_toReal_sum_eq_one`.
