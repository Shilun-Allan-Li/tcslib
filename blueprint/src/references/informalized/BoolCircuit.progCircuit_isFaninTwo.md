<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.progCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in of the program circuit

**Claim.** The circuit built from any program is well formed, has no repeated gate inputs, every NOT gate has exactly one input, and every gate has at most two inputs.

**Proof.** The established gate invariant (BoolCircuit.faninTwo_progGates) gives all three properties for every gate in the full list of program gates. The circuit uses exactly that list, so its well-formedness follows from the first two properties, and its fan-in bound follows from the third.

**Key facts.** `BoolCircuit.faninTwo_progGates`.
