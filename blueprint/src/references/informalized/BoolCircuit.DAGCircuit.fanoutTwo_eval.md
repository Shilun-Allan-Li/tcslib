<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwo_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by fanout reduction

**Claim.** For every assignment $x$ to the input vertices, the circuit obtained from $C$ by the fanout-two construction has the same output value as $C$.

**Proof.** The invariant for the fanout-two construction says that each old vertex retains its value at its corresponding tap vertex: for every input assignment and every old vertex in range, the value at the tap in the constructed gate list equals the value at that vertex in the original gate list (`foGates_inv`). First, the fan-in-two hypothesis supplies the required gate conditions—distinct arguments, one argument for each NOT gate, and at most two arguments (`gates_ok_of_isFaninTwo`). The circuit’s acyclicity and these gate conditions allow the invariant to be applied to the full gate list. Since the designated output is in range, the invariant at that vertex identifies the two output values, as claimed.

**Key facts.** `BoolCircuit.gates_ok_of_isFaninTwo`, `BoolCircuit.foGates_inv`.
