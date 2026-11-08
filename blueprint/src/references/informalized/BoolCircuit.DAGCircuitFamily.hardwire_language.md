<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuitFamily.hardwire_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hardwired circuit language

**Claim.** For each input length, fixing the designated extra input bits of the circuit to the chosen assignment makes the resulting family accept exactly those words whose concatenation with that assignment is accepted by the original circuit.

**Proof.** Take any word $w$. By the characterization of membership in a circuit family's language, it belongs to the hardwired family's language exactly when the circuit obtained by hardwiring the extra inputs into $D_{|w|}$ accepts $w$ (BoolCircuit.DAGCircuitFamily.mem_language_iff). The evaluation theorem for hardwiring says that this is exactly the evaluation of $D_{|w|}$ on the concatenation of $w$'s input assignment with the fixed assignment $\alpha_{|w|}$ (BoolCircuit.DAGCircuit.hardwire_eval). Thus, for every $w$, membership in the left-hand language is equivalent to the stated acceptance condition, proving equality of the languages.

**Key facts.** `BoolCircuit.DAGCircuitFamily.mem_language_iff`, `BoolCircuit.DAGCircuit.hardwire_eval`.
