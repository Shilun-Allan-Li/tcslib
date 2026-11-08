<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean :: CommunicationComplexity.FiniteProbabilitySpace.exists_pmf_toReal_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A point of positive probability

**Claim.** Every finite probability space has some point whose associated probability mass has strictly positive real value.

**Proof.** Suppose instead that every point has nonpositive real mass. Each mass is also nonnegative, so every one must be zero. The finite sum of all real masses would then be zero. But the masses sum to one, a contradiction. Hence some point has strictly positive mass.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.pmf_toReal_sum_eq_one`.
