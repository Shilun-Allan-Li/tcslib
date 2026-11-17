<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.unfoldVertex_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for unfolded circuits

**Claim.** For a well-formed Boolean directed acyclic circuit whose gates have at most $k$ arguments, unfolding any in-range vertex with sufficient fuel produces a tree of size at most $(k+1)^{d(v)}$.

**Proof.** We argue by induction on the fuel. With zero fuel, the hypotheses that the vertex is in range and below the fuel bound cannot both hold. For positive fuel, first suppose $v$ is an input vertex. Its unfolding is a single literal, of size $1$, which is at most $(k+1)^{d(v)}$.

Otherwise, $v$ is the vertex of a gate. The bound on $v$ gives a valid gate index, and acyclicity says that every argument vertex $a$ of this gate satisfies $a<v$. Since also $v<\mathrm{fuel}+1$, each such $a$ is below the available fuel, so the induction hypothesis bounds the unfolding at $a$ by $(k+1)^{d(a)}$. The depth strictly decreases along each argument edge (\texttt{depthAt\_lt\_of\_arg}), hence these sizes are at most $(k+1)^{d(v)-1}$.

The gate is well formed, and has at most $k$ arguments. The gate-unfolding size bound (\texttt{unfoldGate\_size\_le}) therefore bounds the resulting tree by $1+k(k+1)^{d(v)-1}$. Because $d(v)\ge 1$, we have $(k+1)^{d(v)}=(k+1)(k+1)^{d(v)-1}$; the preceding bound is no larger, proving the result.

**Key facts.** `BoolCircuit.DAGCircuit.args_lt_vertex`, `BoolCircuit.DAGCircuit.depthAt_gate`, `BoolCircuit.DAGCircuit.depthAt_lt_of_arg`, `BoolCircuit.DAGCircuit.getD_gates`, `BoolCircuit.unfoldGate_size_le`.
