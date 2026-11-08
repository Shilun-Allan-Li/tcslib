<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniform.lean :: BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time uniformity

**Claim.** If a circuit family is logspace-uniform, then a polynomial-time-computable function outputs the encoding of its $n$th circuit on unary input of length $n$; hence the family is polynomial-time-uniform.

**Proof.** Take a function $f$ witnessing logspace uniformity, so that on each unary input of length $n$ it outputs the encoding of the $n$th circuit. The theorem that every implicitly logspace-computable function is polynomial-time-computable (Complexity.ImplicitlyLogspaceComputable.polyTimeComputable) supplies the required polynomial-time bound for this same $f$. Keeping its unary-input encoding property gives polynomial-time uniformity.

**Key facts.** `Complexity.ImplicitlyLogspaceComputable.polyTimeComputable`.
