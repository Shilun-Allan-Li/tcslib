<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.step_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Halted Configuration Is Fixed

**Claim.** If a configuration has empty state, then one step of the machine leaves that configuration unchanged.

**Proof.** The step rule checks the configuration's state. When that state is empty, the halted branch returns the configuration itself, so the result of one step is exactly the original configuration.
