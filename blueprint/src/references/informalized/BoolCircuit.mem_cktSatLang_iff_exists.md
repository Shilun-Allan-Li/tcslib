<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.mem_cktSatLang_iff_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Satisfiability Language

**Claim.** A bit string belongs to the language of encodings of satisfiable Boolean circuit trees exactly when it is the encoding of some satisfiable Boolean circuit tree.

**Proof.** If a bit string belongs to the language, it decodes to some circuit tree $C$ that is satisfiable. The decoding-and-reencoding property ($\texttt{BoolCircuit.encodeSigma_of_decodeSigma}$) shows that re-encoding $C$ recovers the original bit string, so $C$ is the required witness. Conversely, suppose the bit string is the encoding of a satisfiable circuit tree $C$. The characterization of encoded circuit satisfiability ($\texttt{BoolCircuit.mem_cktSatLang_iff}$) says that this encoding belongs to the language, as required.

**Key facts.** `BoolCircuit.encodeSigma_of_decodeSigma`, `BoolCircuit.mem_cktSatLang_iff`.
