<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/KLDivergence.lean :: ProbabilityTheory.toReal_klDiv_bool_eq_KLDiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary divergence identity

**Claim.** For probability measures on the Boolean space, when the second measure assigns positive mass to each point, the real-valued measure-theoretic KL divergence equals the finite-distribution KL divergence.

**Proof.** The finite-space formula for measure-theoretic KL divergence expresses it as either infinity, if the first measure charges a point where the second has zero mass, or the real part of the sum of pointwise log terms, together with the difference of the total masses (`CommunicationComplexity.FiniteMeasureSpace.klDiv_eq_sum_log`). The positivity assumption on the second measure rules out the exceptional infinite case. Since both measures are probabilities, their total masses are one, so the correction term vanishes. The remaining sum is exactly the finite-distribution KL divergence. Its nonnegativity ensures that taking the real value of its nonnegative extended-real representation leaves that sum unchanged.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.klDiv_eq_sum_log`.
