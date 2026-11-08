<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.negOut_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Complementation Along a Run

**Claim.** For every number of steps, running the machine with each transition’s output complemented from the configuration with its existing output bits complemented gives the same configuration as running the original machine and then complementing its output bits.

**Proof.** Apply the step-commutation theorem (`negOut_step`): one step of the modified machine after complementing a configuration equals complementing the result of one original-machine step. The general run-commutation theorem (`runFrom_comm_of_step`) iterates this one-step identity for any number of steps, yielding the claimed equality.

**Key facts.** `Complexity.negOut_step`, `Turing.OracleTM.runFrom_comm_of_step`.
