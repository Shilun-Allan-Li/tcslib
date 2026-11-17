<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.edge_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Edge Characterization

**Claim.** If the gate at index $V-n$ is $g$ and $n\le V$, then $U$ is an argument of $g$ exactly when there is an edge from vertex $U$ to vertex $V$.

**Proof.** By definition, an edge from $U$ to $V$ means that $n\le V$ and that some gate at index $V-n$ exists whose argument list contains $U$. The assumed lookup identifies that gate as $g$. Since $n\le V$ is already given, the edge condition is therefore equivalent to $U\in g.args$.
