<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.subW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding a Circuit Difference

**Claim.** Under the decoding and well-formedness hypotheses, the circuit-difference construction encodes the circuit formed by concatenating the gates of $C$, the gates of $C'$ shifted by the size of $C$, and a final subtraction gate connecting the two circuit outputs.

**Proof.** The decoding hypotheses imply that each input component is exactly the encoding of its circuit (`Randomized.AlgCircuit.encode_of_decode`). The scan-run result identifies the stored index for each circuit with its size (`Randomized.PIT.sI_scanRun`), using the corresponding well-formedness hypothesis. The shift-run theorem then converts the two shift-run terms into the gate bodies: the first gives the gates of $C$, and the second gives the gates of $C'$ with references shifted by $C.size$ (`Randomized.PIT.shiftRun_eq`). The transducer identities on unary natural encodings (`Complexity.BinArith.uRest_encodeNat` and `Complexity.BinArith.uHead_encodeNat`) recover the encoded input count and the remaining gate-list components. Since $C$ is nonempty, its size is positive. Consequently, dropping the first marker from the concatenation of unary strings of lengths $C.size$ and $C'.size$ leaves the unary encoding of $C.size+C'.size-1$; this is the index of the final subtraction gate. Finally, the gate-list encoding is exactly the concatenation of gate bodies followed by its terminator (`Randomized.PIT.encodeGates_eq`). Substituting these identities into the definition of the difference construction yields the encoding of the circuit with the stated appended gates and subtraction gate.

**Key facts.** `Randomized.AlgCircuit.encode_of_decode`, `Randomized.PIT.sI_scanRun`, `Complexity.BinArith.uRest_encodeNat`, `Randomized.PIT.shiftRun_eq`, `Complexity.BinArith.uHead_encodeNat`, `Randomized.PIT.encodeGates_eq`.
