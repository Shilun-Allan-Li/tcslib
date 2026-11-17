<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.deMorgan_kind_ne_or -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absence of OR gates after De Morgan transformation

**Claim.** If every gate of a circuit has distinct arguments and each NOT gate has exactly one argument, then the circuit obtained by the De Morgan transformation contains no OR gates.

**Proof.** The rewrite theorem guarantees that each gate in the rewritten circuit satisfies the property assigned to the emitted gates (`DAGCircuit.rewrite_new_gates`). For this transformation the property is `DAGGate.NoOr C.size`, whose second component says that the gate kind is not OR. Hence every gate in the De Morgan transformed circuit is not an OR gate.

**Key facts.** `BoolCircuit.DAGCircuit.rewrite_new_gates`.
