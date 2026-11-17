<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.DAGCircuit.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded circuit

**Claim.** For every finite acyclic Boolean circuit $C$ with $n$ inputs, decoding its Boolean-string encoding returns exactly the pair $(n,C)$.

**Proof.** Decode the encoding in its successive parts. The unary natural-number encoding of $n$ decodes to $n$ and leaves the encoded gate list and output number (`decodeNat_encodeNat`). The gate-list encoding then decodes to the original gates, leaving the output encoding; this applies because each gate's own encoding decodes to that gate while preserving any trailing string (`DAGGate.decode_encode`), and the list decoder has enough fuel since the encoding length is at least the number of gates plus one (`length_encodeList_ge`). The remaining unary encoding decodes to the original output number. Finally, the validity check reconstructs $C$ from its parts (`DAGCircuit.ofParts_self`), so the decoder's result is exactly $(n,C)$.

**Key facts.** `BoolCircuit.length_encodeList_ge`, `BoolCircuit.decodeNat_encodeNat`, `BoolCircuit.decodeList_encodeList`, `BoolCircuit.DAGGate.decode_encode`, `BoolCircuit.decodeNat_encodeNat`, `BoolCircuit.DAGCircuit.ofParts_self`.
