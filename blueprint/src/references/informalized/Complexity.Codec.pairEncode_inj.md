<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean :: Complexity.Codec.pairEncode_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Pair Encoding

**Claim.** If two pair encodings of bit strings are equal, then their first components are equal and their second components are equal.

**Proof.** View each pair of bit strings as an element of the product type. The pair encoding is injective on such pairs (`Turing.pairEncode_injective`). Applying this fact to the two encoded pairs gives equality of their first components and equality of their second components.

**Key facts.** `Turing.pairEncode_injective`.
