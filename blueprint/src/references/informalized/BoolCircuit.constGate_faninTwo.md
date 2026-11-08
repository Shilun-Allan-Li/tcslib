<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.constGate_faninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in bound for constant gates

**Claim.** For either Boolean value, the corresponding constant gate is well formed and has at most two input vertices.

**Proof.** A constant gate has an empty argument list, so its arguments have no repetitions and its argument count is at most two. Its kind is not NOT (`constGate_kind_ne_not`), so the implication requiring a NOT gate to have exactly one argument holds vacuously. Together these establish well-formedness and the claimed fan-in bound.

**Key facts.** `BoolCircuit.constGate_kind_ne_not`.
