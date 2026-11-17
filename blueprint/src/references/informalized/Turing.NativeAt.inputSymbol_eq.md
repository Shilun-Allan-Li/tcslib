<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.NativeAt.inputSymbol_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Symbol at a Given Position

**Claim.** If a configuration’s input head is at position $i$, then the symbol it reads is the input-cell value at position $i$.

**Proof.** For every configuration, its scanned symbol equals the input-cell value at its own input-head position (`Cfg.inputSymbol_eq_inputCell`). The NativeAt hypothesis identifies that position with $i$, so substituting it yields the claim.

**Key facts.** `Turing.Cfg.inputSymbol_eq_inputCell`.
