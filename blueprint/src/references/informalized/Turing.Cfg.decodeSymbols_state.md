<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.decodeSymbols_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Preservation Under Decoding

**Claim.** Decoding a configuration preserves its optional machine state, including whether it is halting.

**Proof.** By definition, decoding constructs the new configuration with state exactly $D$’s state. Thus the two state fields are equal.
