<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.bits_eq_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Least Significant Bit Decomposition

**Claim.** For every nonzero natural number $w$, its binary expansion written from least significant bit to most significant bit begins with the bit indicating whether $w$ is odd, followed by the binary expansion of $\lfloor w/2\rfloor$.

**Proof.** The binary-expansion head identity (`LogProg.bits_head_odd`) identifies the first bit of the expansion of nonzero $w$ as the indicator of whether $w$ is odd. The half identity (`LogProg.bits_half`) says that the expansion of $w/2$ is the tail of the expansion of $w$. The expansion cannot be empty, since its head identity for nonzero $w$ gives a present first bit. Writing it as a head followed by a tail, these two identities identify that head and tail as claimed.

**Key facts.** `Complexity.LogProg.bits_head_odd`, `Complexity.LogProg.bits_half`.
