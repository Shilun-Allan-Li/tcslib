<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReduction.lean :: BoolCircuit.CktSatReduction.dagCktSatToSAT3_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-to-3-CNF Serialization

**Claim.** The circuit-to-SAT3 output has the stated form: when the input encodes a valid fan-in-two circuit, it is the output prefix followed by the emitted gate clauses; otherwise it is the serialization of the single empty clause.

**Proof.** Unfold the definitions of the reduction and validity, then split according to whether decoding the input string succeeds. If decoding fails, both sides reduce to the serialization of the single empty clause. If it succeeds with a circuit $C$, the decoding correctness fact (`DAGCircuit.encode_of_decode`) identifies the input with $C$'s encoding. Split on whether $C$ is fan-in-two. In the valid case, the reduction uses $C$'s CNF. The description-tail identity (`descTail_encode`) supplies the unary output index in the output prefix, and the emitter identity (`gateClauses_encode`) identifies the emitted suffix with the serialization of the Tseitin clauses for the gates. Expanding the serialization then gives the claimed output. In the invalid case, the reduction again selects the single empty clause, as claimed.

**Key facts.** `BoolCircuit.DAGCircuit.encode_of_decode`, `BoolCircuit.CktSatReduction.descTail_encode`, `BoolCircuit.CktSatReduction.Emitter.gateClauses_encode`.
