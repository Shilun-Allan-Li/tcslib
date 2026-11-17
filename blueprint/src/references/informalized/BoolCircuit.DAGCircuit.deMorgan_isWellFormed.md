<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.deMorgan_isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Well-formedness after De Morgan transformation

**Claim.** If every gate of a well-formed circuit has distinct arguments and each NOT gate has exactly one argument, then every gate in its De Morgan transformation has distinct arguments, and each transformed NOT gate has exactly one argument.

**Proof.** Apply the rewrite theorem that every gate in a rewritten circuit satisfies the property prescribed for the emitted gates (`DAGCircuit.rewrite_new_gates`). For the De Morgan rewrite, that prescribed property is `DAGGate.NoOr C.size`; its first component is precisely gate well-formedness. Thus each transformed gate has distinct arguments, and its NOT gates have exactly one argument.

**Key facts.** `BoolCircuit.DAGCircuit.rewrite_new_gates`.
