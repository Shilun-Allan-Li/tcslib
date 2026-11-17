<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.constGate_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True constant gate

**Claim.** A constant gate labelled by true is the AND gate with no input vertices.

**Proof.** By definition, the gate label is chosen by testing the Boolean value: for true the conditional selects AND. The argument list is empty, so the constant gate is exactly the AND gate with no inputs.
