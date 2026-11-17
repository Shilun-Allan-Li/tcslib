<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedDecodingValue_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding value bounded by optimum

**Claim.** For a regular unique game with a nonempty label set, the expected decoding value obtained from the influential coordinates of the table and their neighbor averages is at most the optimum value of the associated constraint satisfaction instance.

**Proof.** The bounded decoding rule determines a family of finite candidate-label sets, one for each vertex. The expected value produced by any such family, using the prescribed default when a set is empty, is at most the optimum of the associated constraint satisfaction instance (`candidateDecodingValue_le_optimum`). Taking the bounded decoding candidates as that family gives the stated bound.

**Key facts.** `FABL.RegularUniqueGame.candidateDecodingValue_le_optimum`.
