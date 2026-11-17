<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.length_bits_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Binary Expansion Length

**Claim.** If $a\le b$, then the length of the binary expansion of $a$ is at most the length of the binary expansion of $b$.

**Proof.** Replace each binary-expansion length by the corresponding binary size, using the equality between size and bit-list length (`Nat.size_eq_bits_len`). Binary size is monotone in its argument (`Nat.size_le_size`), so $a\le b$ implies the desired inequality.
