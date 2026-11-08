<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedOrdinaryDecodingEdgeValue_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative ordinary decoding edge value

**Claim.** For any regular unique game, bounded function table, threshold, default label, vertex, and neighbor, the ordinary decoding edge value is nonnegative.

**Proof.** The ordinary decoding candidates form a family of finite candidate-label sets, one for each vertex. The edge value defined from any such family is nonnegative (`candidateDecodingEdgeValue_nonneg`). Applying this result to the ordinary decoding candidates proves the claim.

**Key facts.** `FABL.RegularUniqueGame.candidateDecodingEdgeValue_nonneg`.
