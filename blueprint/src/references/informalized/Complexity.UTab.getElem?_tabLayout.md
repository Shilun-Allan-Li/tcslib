<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.getElem?_tabLayout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Positions in the Table Layout

**Claim.** For natural numbers $N$ and $k$ with $k<N$, the entry at position $k$ in the list of the first $N$ input-bit sources is the source for input bit $k$.

**Proof.** By definition, the table layout is obtained by mapping the input-source constructor over the list $[0,1,\ldots,N-1]$. Since $k<N$, position $k$ in that range is $k$ itself; mapping therefore gives the source for input bit $k$.
