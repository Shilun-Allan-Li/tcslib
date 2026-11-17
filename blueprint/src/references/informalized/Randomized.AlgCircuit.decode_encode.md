<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded circuit

**Claim.** For every finite input arity $n$ and every arithmetic circuit $C$ with $n$ inputs, decoding the Boolean-list encoding of $C$ returns $C$ exactly.

**Proof.** Write the circuit as its input arity together with its gate list. The natural-number decoder recovers the arity and leaves the encoded gate list untouched (`decodeNat_encodeNat`). The gate-list parser then recovers the original gates: the encoding is long enough to use its own length as the parser's fuel (`length_encodeGates`), and parsing succeeds for any fuel at least the number of gates (`parseGates_encodeGates`). Finally, the decoder's encoding check holds because the recovered arity and gates are exactly those originally encoded. Hence decoding returns the original circuit.

**Key facts.** `BoolCircuit.decodeNat_encodeNat`, `Randomized.AlgCircuit.length_encodeGates`, `Randomized.AlgCircuit.parseGates_encodeGates`.
