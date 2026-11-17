<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.decode_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Quantified Formula

**Claim.** Decoding the pair encoding of a Boolean quantifier word and a serialized CNF formula returns the QBF with the corresponding quantifier prefix and that CNF matrix.

**Proof.** The pair decoder inverts the pair encoding, so decoding recovers the original quantifier word and the serialized matrix (`Turing.pairDecode_pairEncode`). The QBF decoder therefore maps each bit of the recovered word to its quantifier and decodes the recovered matrix. By correctness of CNF serialization and decoding, that matrix is the original formula (`Std.Sat.CNF.decode_serialize`). Thus the result is exactly the stated QBF.

**Key facts.** `Turing.pairDecode_pairEncode`, `Std.Sat.CNF.decode_serialize`.
