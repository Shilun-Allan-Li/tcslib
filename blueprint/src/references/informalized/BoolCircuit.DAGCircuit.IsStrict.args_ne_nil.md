<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.IsStrict.args_ne_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Gates Have Arguments

**Claim.** Let $C$ be a finite Boolean circuit in which every gate has distinct arguments and has exactly one argument if it is a NOT gate, and exactly two arguments otherwise. Suppose every vertex other than the output has positive fan-out. Then every gate has a nonempty argument list.

**Proof.** For any gate in $C$, strictness gives its prescribed argument-list length: one for a NOT gate and two for any other gate. In either case the length is positive, so the list cannot be empty. This is the gate-level fact `DAGGate.Strict.args_ne_nil`, applied to each gate using the strictness hypothesis.

**Key facts.** `BoolCircuit.DAGGate.Strict.args_ne_nil`.
