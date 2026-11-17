<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.xorCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of the XOR circuit

**Claim.** The specified XOR circuit is well formed and every gate has at most two arguments.

**Proof.** Inspect each of the circuit's gates in turn. For each gate, its argument list has no repeated indices; whenever the gate is a negation gate, that list has length one. The argument lists of all gates have length at most two. These checks establish well-formedness and the asserted fan-in bound.
