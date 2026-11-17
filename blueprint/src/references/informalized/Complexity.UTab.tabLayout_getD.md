<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.tabLayout_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tabulated Input Source

**Claim.** If $k<N$, then the $k$-th entry of the length-$N$ input-source list is the source for input bit $k$.

**Proof.** The list is formed by taking the natural numbers from $0$ through $N-1$ and replacing each number by the corresponding input-bit source. Since $k<N$, the $k$-th entry of that range is $k$ itself. Mapping the source constructor over the range therefore gives the input source for bit $k$; the default source is unused because the index is in range.
