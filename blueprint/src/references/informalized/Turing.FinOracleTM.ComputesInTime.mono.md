<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleFinite.lean :: Turing.FinOracleTM.ComputesInTime.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of computation time

**Claim.** If the finite-state deterministic oracle machine computes output $y$ from input $x$ in $t$ steps, then it computes the same output in every number $t'\ge t$ of steps.

**Proof.** The finite-state machine is viewed through its underlying oracle Turing machine. The oracle-machine monotonicity theorem says that once a run has halted with a given output, the run remains halted with that output at every later time (\texttt{Turing.OracleTM.ComputesInTime.mono}). Applying this fact to the given computation and the inequality $t\le t'$ gives the result.

**Key facts.** `Turing.OracleTM.ComputesInTime.mono`.
