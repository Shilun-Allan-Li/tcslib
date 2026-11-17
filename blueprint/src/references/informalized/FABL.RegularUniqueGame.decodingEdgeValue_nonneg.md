<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.decodingEdgeValue_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding edge value is nonnegative

**Claim.** For every vertex and neighbor, the decoding edge value obtained by averaging the permutation-consistency indicator over the candidate sets at the two endpoints is nonnegative.

**Proof.** Apply the general nonnegativity result for candidate decoding edge values (`FABL.RegularUniqueGame.candidateDecodingEdgeValue_nonneg`) to the particular candidate sets formed by the decoding procedure. The decoding edge value is precisely that candidate decoding edge value, so the result follows directly.

**Key facts.** `FABL.RegularUniqueGame.candidateDecodingEdgeValue_nonneg`.
