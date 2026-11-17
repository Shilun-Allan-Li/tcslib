<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.unfoldVertex_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of Bounded Unfolding

**Claim.** For a well-formed circuit and input assignment $x$, unfolding a valid vertex $v$ with sufficient fuel and polarity $p$ evaluates to its circuit value when $p$ is true, and to the negation of that value when $p$ is false.

**Proof.** Induct on the fuel. Fuel zero is impossible under the hypothesis $v<f$. For positive fuel, if $v$ is an input vertex, its unfolding is the corresponding literal with sign determined by $p$. The circuit's value list agrees with $x$ at input vertices (`BoolCircuit.DAGCircuit.values_getD_input`), so the literal has the asserted value. If $v$ is a gate vertex, it corresponds to a valid gate index. The circuit value at $v$ is that gate applied to the circuit values (`BoolCircuit.DAGCircuit.values_getD_gate`), and the stored gate entry is the gate at that index (`BoolCircuit.DAGCircuit.getD_gates`). Every argument has smaller index than $v$ (`BoolCircuit.DAGCircuit.args_lt_vertex`), so the induction hypothesis gives the required evaluation identity for each recursively unfolded argument, for either polarity. The evaluation rule for unfolding a well-formed gate then identifies the whole tree's evaluation with the gate's value, or its negation according to the polarity (`BoolCircuit.unfoldGate_eval`).

**Key facts.** `BoolCircuit.DAGCircuit.values_getD_input`, `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.DAGCircuit.args_lt_vertex`, `BoolCircuit.DAGCircuit.getD_gates`, `BoolCircuit.unfoldGate_eval`.
