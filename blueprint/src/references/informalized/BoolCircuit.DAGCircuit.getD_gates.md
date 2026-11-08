<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.getD_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Defaulted gate lookup

**Claim.** If $i$ is less than the number of gates of $C$, then lookup at index $i$ with the constant-true gate as default equals the gate at index $i$.

**Proof.** Because $i$ is within the list’s length, defaulted lookup agrees with ordinary indexed lookup (`List.getD_eq_getElem`). Thus the default value is irrelevant, and the two lookups are equal.
