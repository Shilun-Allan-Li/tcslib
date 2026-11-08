<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.unfoldVertex_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Bound for Bounded Unfolding

**Claim.** For any fuel $f$, vertex $v$, and polarity $p$, if $v$ is a circuit vertex and $v<f$, then the depth of its unfolding is at most the depth assigned to $v$ by $C$.

**Proof.** Proceed by induction on the fuel. Fuel zero cannot satisfy $v<f$. With positive fuel, first consider an input vertex: its unfolding is a literal, of depth zero, and therefore has depth at most the input vertex's assigned depth. Otherwise $v$ corresponds to a gate. Every argument of that gate has index less than $v$ (`BoolCircuit.DAGCircuit.args_lt_vertex`), so the induction hypothesis applies to each argument's unfolding. Each argument also has strictly smaller assigned depth than $v$ (`BoolCircuit.DAGCircuit.depthAt_lt_of_arg`). Thus every argument tree has depth at most $\mathrm{depth}(v)-1$. The assigned depth at a gate is one plus the maximum assigned depth of its arguments (`BoolCircuit.DAGCircuit.depthAt_gate`); the gate's stored list entry is indeed the gate at that vertex (`BoolCircuit.DAGCircuit.getD_gates`). The depth bound for unfolding a well-formed gate then gives depth at most $\mathrm{depth}(v)$ (`BoolCircuit.unfoldGate_depth_le`).

**Key facts.** `BoolCircuit.DAGCircuit.args_lt_vertex`, `BoolCircuit.DAGCircuit.depthAt_gate`, `BoolCircuit.DAGCircuit.depthAt_lt_of_arg`, `BoolCircuit.DAGCircuit.getD_gates`, `BoolCircuit.unfoldGate_depth_le`.
