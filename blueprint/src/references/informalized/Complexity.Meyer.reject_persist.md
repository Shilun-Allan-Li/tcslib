<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.reject_persist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Persistence of Rejection

**Claim.** If the tabulating machine is halted with output $[0]$ after $s$ steps, then after any $s'\ge s$ steps it remains halted with output $[0]$.

**Proof.** Write $s'=s+(s'-s)$, which is possible because $s\le s'$. By the run-addition law (`Turing.MultiTapeTM.runFrom_add`), the run of length $s'$ is the run of length $s'-s$ starting from the configuration reached after $s$ steps. That configuration is halted by hypothesis, and a run starting from a halted configuration leaves it unchanged (`Turing.MultiTapeTM.runFrom_of_halt`). Thus the later configuration equals the one at time $s$, so it is still halted and its output is still $[0]$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
