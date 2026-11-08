<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedDecodingEdgeValue_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative bounded decoding edge value

**Claim.** For any regular unique game, bounded function table, threshold, default label, vertex, and neighbor, the ordinary decoding edge value is nonnegative.

**Proof.** The bounded decoding candidates specify a finite candidate-label set at each vertex. The edge value formed from these sets is nonnegative for every such family of candidate sets (`candidateDecodingEdgeValue_nonneg`). Applying that fact to the bounded decoding candidates yields the claim.

**Key facts.** `FABL.RegularUniqueGame.candidateDecodingEdgeValue_nonneg`.
