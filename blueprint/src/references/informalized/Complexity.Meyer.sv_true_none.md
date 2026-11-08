<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.sv_true_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Symbol Interpretation of Symbolic Answers

**Claim.** For every sign $s$ and $t,a<2^W$, the symbolic answer for the absent-tape selector equals the input symbol read at the signed displacement $(-1)^s a$ from the input head.

**Proof.** The table-agreement hypothesis replaces each of the two selector answers defining the symbolic answer by the corresponding tabulated answer for the run's configuration. The absent-tape decoding rule (`Complexity.Meyer.tabAns_sym_none`) expresses these two bits as the indicators for whether the input symbol at signed displacement $(-1)^s a$ is blank or true. Decoding those two indicators recovers the option-valued symbol itself (`Complexity.Meyer.decode_symBit`), proving the equality with the configuration's input read at that displacement.

**Key facts.** `Complexity.Meyer.tabAns_sym_none`, `Complexity.Meyer.decode_symBit`.
