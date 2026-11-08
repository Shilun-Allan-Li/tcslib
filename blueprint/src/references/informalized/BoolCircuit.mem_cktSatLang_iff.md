<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Encoding.lean :: BoolCircuit.mem_cktSatLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding and Satisfiability

**Claim.** The encoding of a Boolean circuit tree belongs to the language of encodings of satisfiable circuit trees exactly when the circuit tree is satisfiable.

**Proof.** Suppose the encoding of a circuit tree $C$ belongs to the language. Then it decodes to some circuit tree $D$ that is satisfiable. The decoding-after-encoding identity ($\texttt{BoolCircuit.decodeSigma_encodeSigma}$) says that the encoding of $C$ decodes back to $C$; comparing this with the decoding to $D$ gives $C=D$. Hence $C$ is satisfiable. Conversely, if $C$ is satisfiable, the same decoding identity shows that its encoding decodes to $C$, so it witnesses membership in the language.

**Key facts.** `BoolCircuit.decodeSigma_encodeSigma`.
