<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.searchCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in bound for the search circuit

**Claim.** If every input circuit has distinct gate arguments, unary negation gates, and at most two arguments per gate, then every gate in the constructed search circuit has those same properties.

**Proof.** Apply the structural theorem for the search state after $m$ stages (`searchState_struct`). Its final assertion gives, for every gate in the state’s gate list, distinct arguments, exactly one argument whenever the gate is a negation, and at most two arguments. The search circuit takes this very gate list as its gates, so these properties are exactly the multiple-output circuit’s fan-in conditions.

**Key facts.** `BoolCircuit.searchState_struct`.
