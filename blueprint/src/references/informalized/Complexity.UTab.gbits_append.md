<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.gbits_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding preserves concatenation

**Claim.** For two finite gate lists, the concatenated prefixed encodings of their concatenation equal the concatenation of their individual prefixed encodings.

**Proof.** The encoding is a list concatenation: each gate contributes the string consisting of one followed by that gate's encoding. Distributing this concatenation over the two joined lists gives the encodings of the first and second lists in succession.
