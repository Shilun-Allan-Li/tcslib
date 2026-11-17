<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalNP.lean :: BoolCircuit.dagCktSatLang_mem_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit satisfiability belongs to NP

**Claim.** The language of valid encodings of satisfiable Boolean directed acyclic circuits with at most two inputs per gate belongs to NP.

**Proof.** Use the NP characterization with certificates whose length is bounded by a polynomial and a polynomial-time language verifier (`Complexity.mem_NP_iff_exists_length_le`). The proof chooses the circuit-value prefix verifier, which belongs to P (`BoolCircuit.CVALPrefix_mem_P`), and takes as certificate the Boolean assignment to the circuit’s input vertices. If an encoded circuit is in the target language, its fan-in-two property and a satisfying assignment give such a certificate; the size bound for the circuit relative to its encoding (`BoolCircuit.DAGCircuit.size_le_length_encode`) ensures the assignment is within the required polynomial length. The verifier accepts the encoded pair precisely when the circuit evaluates to true on that assignment. Conversely, an accepting certificate decodes, by injectivity of pair encoding (`Turing.pairEncode_injective`), to the original input and certificate pair; the verifier’s acceptance then supplies a fan-in-two circuit and a satisfying assignment for the original encoding. Thus the verifier characterization holds, proving NP membership.

**Key facts.** `Complexity.mem_NP_iff_exists_length_le`, `BoolCircuit.CVALPrefix_mem_P`, `BoolCircuit.DAGCircuit.size_le_length_encode`, `Turing.pairEncode_injective`.
