<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/KLDivergence.lean :: ProbabilityTheory.toReal_klDiv_map_bool_eq_KLDiv_of_measureReal_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional pushforward divergence identity

**Claim.** If the conditioning event has positive measure and the reference probability measure assigns positive mass to each Boolean value, then the real-valued KL divergence of the conditional measure pushed forward by the Boolean-valued map equals the corresponding finite-distribution divergence.

**Proof.** Positive measure of the conditioning event makes the conditional measure a probability measure. A measurable map sends a probability measure to a probability measure under pushforward, so the Boolean-valued pushforward is also a probability measure. Apply the binary divergence identity to that pushforward and the reference measure. Unfolding the finite-distribution divergence for the pushforward gives the claimed expression for the map and the conditional measure.

**Key facts.** `ProbabilityTheory.toReal_klDiv_bool_eq_KLDiv`.
