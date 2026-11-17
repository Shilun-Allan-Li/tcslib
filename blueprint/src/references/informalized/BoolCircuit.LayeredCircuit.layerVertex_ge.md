<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.layerVertex_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Layer Vertex Indices

**Claim.** If $m+1<\mathrm{depth}(F)+1$ and $u$ is a node in layer $m+1$, then its assigned index is at least $n$ plus the cumulative number of nodes in successor layers preceding layer $m$.

**Proof.** By definition, the index assigned to a node in layer $m+1$ is $n+\mathrm{offset}(m)$ plus the value of its image under the layer enumeration. That enumeration takes values in the natural numbers, so its value is nonnegative. The assigned index is therefore at least $n+\mathrm{offset}(m)$.
