<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuitFamily.HasFaninTwo.isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanin two implies well formedness

**Claim.** If every circuit in a family is well formed and every gate has at most two arguments, then the family is well formed.

**Proof.** Fix an input length $n$. The fan-in-two hypothesis at $n$ includes, as its first component, the assertion that the circuit for that input length is well formed. Since $n$ was arbitrary, the family is well formed.
