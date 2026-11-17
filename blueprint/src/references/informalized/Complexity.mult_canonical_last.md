<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_canonical_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonicality and the Last Bit

**Claim.** A bit string $w$ is canonical exactly when it is empty or its bit at position $|w|-1$ is true, interpreting a missing entry as false.

**Proof.** Split into the empty and nonempty cases. For the empty string, canonicality holds vacuously, and the disjunction holds by its first alternative. If $w$ is nonempty, then its length is positive, and the bit at position $|w|-1$ is its last bit. Thus the disjunction reduces to that last bit being true. This is precisely the condition that the last bit is true for every proof that $w$ is nonempty, which is the definition of canonicality.
