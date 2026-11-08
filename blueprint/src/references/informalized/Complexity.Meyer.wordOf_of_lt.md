<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigma.lean :: Complexity.Meyer.wordOf_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Word Enumeration

**Claim.** Whenever $v<2^W$, the word assigned to $v$ at width $W$ is exactly its width-$W$ little-endian binary enumeration, including any high-order zero bits.

**Proof.** By definition, `wordOf` returns `enumWord W v` when $v<2^W$ and returns the empty word otherwise. Under the given bound, the first branch applies, so the result is `enumWord W v`.
