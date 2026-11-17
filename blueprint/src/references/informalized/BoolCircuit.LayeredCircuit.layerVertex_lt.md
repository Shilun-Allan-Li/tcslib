<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.layerVertex_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Layer Vertex Indices

**Claim.** For every layer $m<\mathrm{depth}(F)+1$ and every node $u$ in that layer, its assigned index is strictly less than $n$ plus the cumulative number of nodes in successor layers preceding layer $m$.

**Proof.** Proceed by the definition of the assigned index, separating layer zero from successor layers. In layer zero, the index is the value of an input in $\mathrm{Fin}(n)$, hence is less than $n$; the offset at zero is zero. In layer $m+1$, the enumeration assigns the node a natural number strictly below the cardinality of that layer. The successor formula for the offset (`offset_succ`) adds the number of nodes in layer $m+1$ to the preceding offset, and the relevant summand is exactly that layer's cardinality. Consequently, adding the enumeration value to $n+\mathrm{offset}(m)$ remains strictly below $n+\mathrm{offset}(m+1)$.

**Key facts.** `BoolCircuit.LayeredCircuit.offset_succ`.
