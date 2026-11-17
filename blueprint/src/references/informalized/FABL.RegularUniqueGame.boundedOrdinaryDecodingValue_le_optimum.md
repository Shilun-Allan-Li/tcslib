<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedOrdinaryDecodingValue_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordinary decoding value bound

**Claim.** For a regular unique game with a nonempty label set, a bounded function table, any threshold, and a default label, the expected edge agreement obtained by choosing uniformly from each vertex’s ordinary decoding candidates (using the default when a candidate set is empty) is at most the optimum value of the associated constraint satisfaction instance.

**Proof.** The ordinary decoding rule supplies a family of finite candidate-label sets indexed by the vertices. For any such family, the resulting expected decoding value is at most the optimum of the associated constraint satisfaction instance (`candidateDecodingValue_le_optimum`). Substituting the ordinary decoding candidates gives the asserted inequality.

**Key facts.** `FABL.RegularUniqueGame.candidateDecodingValue_le_optimum`.
