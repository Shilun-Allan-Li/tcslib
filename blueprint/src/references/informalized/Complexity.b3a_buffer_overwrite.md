<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_buffer_overwrite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overwriting the first buffer cell

**Claim.** For every Boolean word $w$ and integer cell position $z$, writing true at cell $0$ on the buffer tape for $w$ produces the same tape contents as the buffer for the word obtained by replacing the first symbol of $w$ with true, or using the one-symbol word true if $w$ is empty.

**Proof.** Split according to whether $z=0$. At the origin, both sides contain true: the left side explicitly writes it, and the first symbol of $\mathrm{true}::w.\mathrm{tail}$ is true. If $z\ne0$, split according to whether $z$ is nonnegative. For nonnegative $z$, its natural-number index is nonzero, so reading from $w$ at that index agrees with reading from its tail at the index one smaller; the modified first symbol does not affect this cell. For negative $z$, both buffer values are blank by definition, and the conditional write at the origin does not apply.
