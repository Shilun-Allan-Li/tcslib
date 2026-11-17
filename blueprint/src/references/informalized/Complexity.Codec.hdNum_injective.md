<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.hdNum_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injective Numbering of Head Descriptors

**Claim.** The enumeration number assigned to a head descriptor is injective: two descriptors with the same number are equal.

**Proof.** The number assigned to a descriptor is the value of its image under the equivalence from the finite type of head descriptors to the corresponding finite ordinal. If two descriptors have the same number, equality of their ordinal values gives equality of their images in that ordinal. Since the equivalence is injective, the original descriptors are equal.
