<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.card_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A finite distribution has outcomes

**Claim.** The finite outcome set of a probability distribution is nonempty, so its cardinality is positive.

**Proof.** Suppose instead that the cardinality were zero. Then the outcome type would be empty, and the sum of the probabilities over all outcomes would be the empty sum, namely zero. This contradicts the defining requirement that the probabilities sum to one. Therefore the cardinality is positive.
