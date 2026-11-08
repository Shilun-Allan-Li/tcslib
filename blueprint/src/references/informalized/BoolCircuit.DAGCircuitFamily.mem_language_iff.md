<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuitFamily.mem_language_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a circuit family's language

**Claim.** A Boolean string $w$ belongs to the language accepted by a circuit family if and only if the circuit for inputs of length $|w|$ evaluates to true on $w$.

**Proof.** By definition, the language consists exactly of the words accepted by the family, and acceptance of $w$ means that the circuit indexed by $w$'s length evaluates to true on $w$.
