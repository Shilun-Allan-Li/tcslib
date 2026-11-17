<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.gates_acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of the Gate List

**Claim.** For every gate in the list constructed from $f$ and $k$, each input vertex at gate index $j$ has index less than $n+j$.

**Proof.** Fix a gate index $j$ within the list and an input vertex $a$ of the gate at that index. The list entry agrees with the gate assigned by the construction at index $j$ (the entry formula, `BoolCircuit.Lupanov.getElem_gates`). The construction’s input bound says that every input of that assigned gate is below $n+j$ (`BoolCircuit.Lupanov.gateAt_args_lt`), using $k\le n$ and the fact that $j$ is within the construction’s range. Thus $a<n+j$, as required.

**Key facts.** `BoolCircuit.Lupanov.getElem_gates`, `BoolCircuit.Lupanov.gateAt_args_lt`.
