<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FanOut.lean :: BoolCircuit.gates_ok_of_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate properties in fan-in-two circuits

**Claim.** If a circuit is well formed and every gate has at most two inputs, then each gate has pairwise distinct inputs, every NOT gate has exactly one input, and every gate has at most two inputs.

**Proof.** Fix a gate in the circuit. The well-formedness assumption supplies both pairwise distinctness of its inputs and the condition that a NOT gate has exactly one input. The fan-in-two assumption supplies the bound of two on its input count. Collecting these three properties gives the asserted conclusion for this gate, and the gate was arbitrary.
