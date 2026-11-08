<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.MultiTapeTM.toNDTM_initCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Preservation

**Claim.** The associated nondeterministic machine and the deterministic machine have the same initial configuration on every input word.

**Proof.** Both initial-configuration definitions construct the configuration from the same initial state, input, blank work tapes, initial head positions, and empty output. The resulting configurations are therefore equal field by field.
