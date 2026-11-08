<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.andAllDAG_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In Bound for the AND Circuit

**Claim.** For every $n$, the circuit formed by combining all $n$ inputs with AND is well formed: each gate has distinct input vertices, every NOT gate has exactly one input, and each gate has at most two inputs.

**Proof.** The specification of the emitted AND tree says that every newly emitted gate has the AND kind, has distinct arguments, and has at most two arguments (`BoolCircuit.andAllDAG_spec`). Since the construction starts with no gates, every gate in the resulting circuit is among these newly emitted gates. The distinctness and arity bound therefore hold for every gate. Also, no such gate is a NOT gate, so the implication requiring a NOT gate to have exactly one input holds vacuously. These are the well-formedness and fan-in-two conditions.

**Key facts.** `BoolCircuit.andAllDAG_spec`.
