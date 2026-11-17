<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.abs_measureReal_sub_le_tvDistance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Event difference bounded by total variation

**Claim.** For any measurable event $S$, the absolute difference between its probabilities under $\mu$ and $\nu$ is at most their total variation distance.

**Proof.** The event bound for a signed difference of probability measures states that the absolute difference $|\mu(S)-\nu(S)|$ is at most one half of the total variation of the signed measure $\mu-\nu$ on the whole space (`event_abs_measureReal_sub_le_half_totalVariation`). By the definition of total variation distance, this latter quantity is exactly $\lVert\mu-\nu\rVert_{TV}$.

**Key facts.** `CommunicationComplexity.TVDistance.event_abs_measureReal_sub_le_half_totalVariation`.
