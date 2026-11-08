<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.hdNum_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Head-Descriptor Numbers

**Claim.** Every head descriptor has an enumeration number strictly smaller than the total number of head descriptors.

**Proof.** The enumeration is an equivalence from the finite type of head descriptors to the finite ordinal whose size is the cardinality of that type. The image of any descriptor is an element of that ordinal, so its value is strictly less than the ordinal's size, which is the total number of head descriptors.
