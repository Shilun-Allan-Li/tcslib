<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.tabLayout_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the Tableau Input Layout

**Claim.** For all natural numbers $N,w$, every bit source in the tableau layout of length $N$ is valid for an input of length $N$, block width $w$, and instruction index $0$.

**Proof.** Any source in the layout is an input source indexed by some $k$ in the range from $0$ to $N-1$. Such a source is valid precisely when its input index is less than $N$, and this is exactly the bound supplied by membership in that range. There are no constant or block sources in this layout, so no further validity conditions arise.
