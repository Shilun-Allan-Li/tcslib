<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.sv_true_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Interpretation of Symbolic Answers

**Claim.** For every work tape $h$, sign $s$, and $t,a<2^W$, the symbolic answer selecting tape $h$ equals the symbol stored at signed displacement $(-1)^s a$ from that tape's head.

**Proof.** Use the table-agreement hypothesis to replace the two selector answers defining the symbolic answer by tabulated answers on the configuration reached at time $t$. The work-tape decoding rule (`Complexity.Meyer.tabAns_sym_some`) identifies these as the blank and true indicators for the symbol at signed displacement $(-1)^s a$ on tape $h$. The decoding identity (`Complexity.Meyer.decode_symBit`) combines those indicators to recover that option-valued symbol, which is the claimed work-tape read.

**Key facts.** `Complexity.Meyer.tabAns_sym_some`, `Complexity.Meyer.decode_symBit`.
