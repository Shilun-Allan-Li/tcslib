<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.DAGCircuit.IsStrict.isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict circuits have fan-in at most two

**Claim.** In a strict circuit, every gate has distinct arguments, each NOT gate has exactly one argument, and every gate has at most two arguments.

**Proof.** Take any gate of the circuit. By strictness, its argument list has no repetitions and has length one when the gate is a NOT gate and length two otherwise. The strict-gate fan-in theorem (`DAGGate.Strict.faninTwo`) packages these properties as well-formedness together with the bound of two on the argument count. Applying it to each gate gives the claimed circuit-wide properties.

**Key facts.** `BoolCircuit.DAGGate.Strict.faninTwo`.
