<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.outputSymbol_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Output Is Prescribed After Halting

**Claim.** If a configuration has empty state, then the machine’s output symbol for that configuration is absent.

**Proof.** By definition, the output-symbol function returns no symbol in the empty-state case. Substituting the hypothesis that the configuration’s state is empty therefore gives the claim immediately.
