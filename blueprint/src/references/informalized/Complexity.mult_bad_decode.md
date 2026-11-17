<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_bad_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failed Decoding Excludes Multiplication Inputs

**Claim.** If parsing a bit string as a pair and then parsing its second component fails, the string is not in the binary multiplication language.

**Proof.** Suppose instead that the string is a multiplication input. By the definition of that language, it is the nested pair encoding of the canonical bit representations of two numbers and their product. Pair decoding reverses pair encoding (Turing.pairDecode_pairEncode), so decoding the outer pair returns its two components, and decoding the second component succeeds as well. This contradicts the assumed failure of the two successive decodings.

**Key facts.** `Turing.pairDecode_pairEncode`.
