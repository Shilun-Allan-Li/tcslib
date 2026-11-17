<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.runFrom_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs from a halted configuration are constant

**Claim.** If a configuration is halted, then running the machine for any number of steps leaves that configuration unchanged.

**Proof.** A halted configuration is fixed by one step: when its state is absent, the machine’s step rule returns the configuration itself (`step_of_halt`). Iterating a function from a fixed point leaves that point unchanged, so every finite run from this configuration equals the starting configuration.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`.
