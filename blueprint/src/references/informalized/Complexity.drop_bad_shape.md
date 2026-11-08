<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_bad_shape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection of Malformed Inputs

**Claim.** If the aligned pair parser cannot decode a bit string $h$, then the indicator of the transformed-input language is false on $h$, for either mode.

**Proof.** If $h$ belonged to the language, its definition would provide strings $z$ and a natural number $q$ such that $h$ is the encoding of $z$ paired with the binary representation of $q$. The pair-encoding decoding identity (Turing.pairDecode_pairEncode) says that every such encoded pair decodes successfully. This contradicts the assumption that parsing $h$ fails. Thus $h$ is outside the language, and its membership indicator is false.

**Key facts.** `Turing.pairDecode_pairEncode`.
