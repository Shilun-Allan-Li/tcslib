<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_transport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transport Under Embeddings

**Claim.** Running the symbol-lifted machine on the embedded configuration agrees with decoding the embedded tapes, running the original machine, and lifting its symbols back, while retaining unused tapes and prefixing the original output.

**Proof.** The restriction identity (`Turing.recordStep_restrict`) expresses the given configuration as an embedded configuration whose simulated tapes are decoded by the Boolean embedding. The hypothesis that every nonblank symbol on an embedded tape lies in the embedding’s image ensures this decoding represents the original tape contents. Starting from this equality, transport the run through the tape embedding using the run identity for embedded machines (`Turing.embedEmitTM_runFrom`), and through the alphabet embedding using the symbol-lifting run identity (`Turing.MultiTapeTM.liftSymbols_runFrom`). The resulting embedded configuration keeps the unused tapes and their head positions, prefixes the original output, and lifts the simulated run’s symbols, as required.

**Key facts.** `Turing.recordStep_restrict`, `Turing.embedEmitTM_runFrom`, `Turing.MultiTapeTM.liftSymbols_runFrom`.
