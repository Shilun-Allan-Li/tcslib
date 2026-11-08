<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwo_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin bound after fanout reduction

**Claim.** The circuit obtained from $C$ by the fanout reduction construction has distinct arguments at every gate, exactly one argument at each NOT gate, and at most two arguments at every gate.

**Proof.** The fanout-two construction’s invariant guarantees that every gate in its resulting list has distinct arguments, that a NOT gate has exactly one argument, and that each gate has at most two arguments (`foGates_inv`). The hypothesis that $C$ has fan-in two supplies the corresponding conditions on its original gates (`gates_ok_of_isFaninTwo`); together with the circuit’s acyclicity, these are the hypotheses needed to apply the invariant. Its gate condition gives all three assertions for the constructed circuit.

**Key facts.** `BoolCircuit.gates_ok_of_isFaninTwo`, `BoolCircuit.foGates_inv`.
