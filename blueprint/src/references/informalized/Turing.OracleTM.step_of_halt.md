<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.step_of_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Halted Configuration Remains Fixed

**Claim.** A step from a configuration with empty state leaves the configuration unchanged.

**Proof.** The step definition branches on the state. When the state is empty, it returns the configuration itself, independently of the oracle language.
