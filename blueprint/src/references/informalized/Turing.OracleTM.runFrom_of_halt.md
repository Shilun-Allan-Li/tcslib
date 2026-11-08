<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs from Halted Configurations

**Claim.** If a configuration is already halted, every finite run of the oracle machine from it leaves the configuration unchanged.

**Proof.** A halted configuration is fixed by one transition, by the one-step halted-configuration theorem (`Turing.OracleTM.step_of_halt`). Iterating a function that fixes the starting configuration any finite number of times still gives that configuration, so the run remains unchanged.

**Key facts.** `Turing.OracleTM.step_of_halt`.
