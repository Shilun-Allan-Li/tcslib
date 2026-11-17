<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwire_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of fan-in at most two

**Claim.** If every gate of $C$ has distinct input vertices, each NOT gate has exactly one input, and every gate has at most two inputs, then hardwiring the last $m$ inputs preserves these properties.

**Proof.** Well-formedness of the new circuit, which gives distinct arguments at each gate and the required arity for NOT gates, follows from `hardwire_isWellFormed`. For the fan-in bound, split a gate of the new circuit according to whether it comes from the prepended constant gates or from $C$. A constant gate has no arguments and therefore has at most two. A gate inherited from $C$ keeps its argument list unchanged, so it retains the original bound of two.

**Key facts.** `BoolCircuit.DAGCircuit.hardwire_isWellFormed`.
