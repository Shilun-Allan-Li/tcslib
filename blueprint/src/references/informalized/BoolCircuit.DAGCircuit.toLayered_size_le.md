<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.toLayered_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for the layered circuit

**Claim.** The size of the layered circuit is at most $(|C.\mathrm{gates}|+1)(\mathrm{size}(C)+1)$, where $\mathrm{size}(C)=n+|C.\mathrm{gates}|$.

**Proof.** The layered-circuit size is the cardinality of the disjoint union of the node types at successor layers. Since each such type is finite, the cardinality of that disjoint union is the sum of the cardinalities of its layers. At a layer indexed by $d$, the node type is $	ext{Fin}(n+d+1)$ if $d+1$ is at most the number of gates, and otherwise it is a singleton. In the first case its cardinality is $n+d+1$, which is at most $n+|C.\mathrm{gates}|+1=\mathrm{size}(C)+1$; in the second case its cardinality is $1$, also at most that bound. There are $|C.\mathrm{gates}|+1$ layers in the sum, so summing the uniform bound gives the result.
