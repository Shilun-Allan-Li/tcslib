<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.Cfg.embedOracle_inputSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Input Symbol Preservation

**Claim.** The optional symbol scanned by the input head is unchanged by embedding the configuration.

**Proof.** Embedding leaves the input-head position unchanged and retains the same input word. The scanned-symbol function depends only on that position and input, so its value is unchanged.
