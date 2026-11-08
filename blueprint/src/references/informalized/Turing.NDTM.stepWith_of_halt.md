<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.stepWith_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halted Configurations Remain Fixed

**Claim.** A step under any choice leaves a configuration with empty state unchanged.

**Proof.** By definition, a step inspects the configuration's state. When that state is empty, the halted branch returns the configuration itself, so the step equals the original configuration.
