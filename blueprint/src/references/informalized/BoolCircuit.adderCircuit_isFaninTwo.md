<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.adderCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adder Circuit Has Fan-In Two

**Claim.** For every natural number $n$, the adder circuit on $n$ input vertices is well formed and each gate reads at most two vertices.

**Proof.** The circuit's gates are exactly the gates in the adder-gate list. Each such gate has pairwise distinct inputs, every negation gate has exactly one input, and every gate has at most two inputs, by the gate-by-gate fan-in theorem (`BoolCircuit.faninTwo_adderGates`). These two properties are the well-formedness and fan-in conditions in the statement, so together they establish the result.

**Key facts.** `BoolCircuit.faninTwo_adderGates`.
