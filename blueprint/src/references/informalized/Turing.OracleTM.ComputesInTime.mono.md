<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.ComputesInTime.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Computation Time

**Claim.** If the machine halts with output $w$ after $t$ steps, then it also halts with output $w$ after any $t'\ge t$ steps.

**Proof.** The hypothesis says that the configuration reached at time $t$ is halted and has output $w$. Write $t'=t+(t'-t)$, which is possible because $t\le t'$. Iterating the step for this sum means first running for $t$ steps and then for $t'-t$ more. A run starting from a halted configuration stays fixed for any number of steps (`Turing.OracleTM.runFrom_of_halt`). Hence the configuration at time $t'$ is exactly the one at time $t$, so it is halted and still has output $w$.

**Key facts.** `Turing.OracleTM.runFrom_add`, `Turing.OracleTM.runFrom_of_halt`.
