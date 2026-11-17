<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwo_hasFanoutTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout bound after fanout reduction

**Claim.** In the circuit obtained from $C$ by the fanout reduction construction, every vertex is read by at most two gates.

**Proof.** The invariant for the fanout-two construction includes the bound that every vertex is read by at most two gates (`foGates_inv`). The hypothesis that $C$ has fan-in two provides the required conditions on its gates (`gates_ok_of_isFaninTwo`), and its circuit structure supplies acyclicity. Applying the invariant to $C$ gives the stated bound for the constructed circuit.

**Key facts.** `BoolCircuit.gates_ok_of_isFaninTwo`, `BoolCircuit.foGates_inv`.
