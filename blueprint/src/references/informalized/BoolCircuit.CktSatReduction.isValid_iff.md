<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.isValid_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Valid Circuit Encodings

**Claim.** A bit string is valid exactly when it encodes a circuit with some number of input vertices, satisfying the stated acyclicity, argument-list, NOT-arity, and fan-in conditions.

**Proof.** For the forward implication, unfold validity and split on whether decoding succeeds. Failure is impossible when the validity indicator is true. On success, validity says the decoded circuit is fan-in-two; the decoding correctness fact (`DAGCircuit.encode_of_decode`) says that its encoding is the original string. This decoded circuit is the required witness. Conversely, suppose a circuit with the stated conditions encodes to the given string. Decoding an encoded circuit recovers that circuit (`DAGCircuit.decode_encode`), so the validity check succeeds because the circuit is fan-in-two.

**Key facts.** `BoolCircuit.DAGCircuit.encode_of_decode`, `BoolCircuit.DAGCircuit.decode_encode`.
