<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.stepWith_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Configurations Are Fixed

**Claim.** When a configuration has no state, stepping the nondeterministic oracle machine leaves it unchanged.

**Proof.** In the definition of the step, the no-state case returns the original configuration immediately. Since the given configuration has no state, this is the applicable case, and the result equals the configuration.
