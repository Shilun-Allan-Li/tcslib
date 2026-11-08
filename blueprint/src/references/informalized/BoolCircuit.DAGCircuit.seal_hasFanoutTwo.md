<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.seal_hasFanoutTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout Bound After Sealing

**Claim.** If each vertex is read by at most two gates and the output is read by at most one gate, then every vertex in the sealed circuit is read by at most two gates.

**Proof.** Use the fanout bound for the sealing construction (`sealGates_fanout`). Its hypotheses are supplied by the circuit's acyclicity and valid output, and by the properties of the dead-vertex list: each listed vertex is a valid vertex, the list has no repetitions, excludes the output, and contains only vertices with zero fanout. The assumed bound gives fanout at most one for the output and at most two for every vertex of the original circuit. The sealing result therefore bounds the fanout of every vertex after sealing by two, which is exactly the claimed property.

**Key facts.** `BoolCircuit.DAGCircuit.mem_deadVertices`, `BoolCircuit.sealGates_fanout`.
