<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.constGate_kind_ne_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant gate is not NOT

**Claim.** For either Boolean value, the corresponding constant gate is not labelled by NOT.

**Proof.** If the value is true, the gate kind is AND; if it is false, the gate kind is OR. Neither kind is NOT, proving the claim in both cases.
