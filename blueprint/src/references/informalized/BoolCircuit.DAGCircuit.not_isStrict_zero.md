<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.not_isStrict_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No strict circuit with zero inputs

**Claim.** There is no directed acyclic circuit with zero input vertices in which every gate has distinct inputs, each NOT gate has exactly one input and every other gate has exactly two inputs, and every vertex other than the output is read by at least one gate.

**Proof.** Suppose such a circuit were strict. Since its output index is less than the number of gates, the gate list is nonempty. Its first gate is strict, so its argument list cannot be empty (`DAGGate.Strict.args_ne_nil`). But acyclicity says that every argument of the first gate has index less than $0+0=0$, which is impossible for a natural number. This contradiction rules out a strict circuit with zero inputs.

**Key facts.** `BoolCircuit.DAGGate.Strict.args_ne_nil`.
