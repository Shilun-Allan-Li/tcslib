<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.mem_dagCktSatLang_iff_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding Circuit Satisfiability Encodings

**Claim.** A Boolean word belongs to the language of encodings of fan-in-two satisfiable DAG circuits exactly when it decodes to a variable-count and circuit pair belonging to the set of fan-in-two satisfiable DAG circuits.

**Proof.** For the forward implication, unpack language membership to obtain a pair $(n,C)$ in the specified set whose encoding is the given word. Since the word is therefore $C$'s encoding, the fact that decoding an encoded circuit recovers the original pair (`DAGCircuit.decode_encode`) gives the required decoded pair; its membership in the set is the original hypothesis. Conversely, suppose the word decodes to a pair $C$ in the set. Membership in that set supplies the witness required by the language definition, and decoding a word to $C$ implies that $C$ encodes back to that word (`DAGCircuit.encode_of_decode`).

**Key facts.** `BoolCircuit.DAGCircuit.decode_encode`, `BoolCircuit.DAGCircuit.encode_of_decode`.
