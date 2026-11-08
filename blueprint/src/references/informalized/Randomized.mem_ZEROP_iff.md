<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.mem_ZEROP_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding Zero Polynomial Circuits

**Claim.** A bit string belongs to the language of encodings of nonempty well-formed arithmetic circuits with zero associated polynomial exactly when it decodes to such a circuit.

**Proof.** For the forward implication, membership supplies a circuit code whose encoding is the given bit string, together with well-formedness and the zero-polynomial condition. The encoding-decoding characterization says that a code is recovered by decoding its encoding (`Randomized.AlgCircuit.decode_eq_some_iff`), so this same circuit witnesses the decoding formulation, retaining the other two properties. Conversely, if decoding the string returns a circuit with those properties, the same characterization converts that decoding equation into the assertion that the circuit encodes the string. The circuit and its well-formedness and polynomial conditions therefore witness membership in the language.

**Key facts.** `Randomized.AlgCircuit.decode_eq_some_iff`.
