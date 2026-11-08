<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.IsStrict.fanout_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero fan-out characterizes the output

**Claim.** For every vertex $v$ below the size of a strict circuit $C$, its fan-out is zero exactly when $v$ is the output.

**Proof.** If $v$ is not the output, strictness says every vertex below the circuit size other than the output has positive fan-out. Thus fan-out zero forces $v$ to be the output. Conversely, the output is the last vertex, by the strict-circuit output theorem (`DAGCircuit.IsStrict.output_eq`). In a topologically ordered acyclic circuit, a vertex at or beyond the final vertex has fan-out zero (`fanoutIn_last_eq_zero`): every gate reads only earlier vertices, so no gate can use that vertex as an argument. Applying this to the output proves the reverse implication.

**Key facts.** `BoolCircuit.DAGCircuit.IsStrict.output_eq`, `BoolCircuit.fanoutIn_last_eq_zero`.
