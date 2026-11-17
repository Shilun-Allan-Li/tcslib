<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.dm_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase Stack Doubling Loop

**Claim.** Starting from any register state bounded by $B$, if $T+2SP\leq B$, the phase-stack doubling loop reaches the move site that copies the phase stack back. It sets $SP$ to zero, replaces $T$ by its initial value plus twice its initial $SP$, leaves all other registers unchanged, and keeps the guard true throughout the run.

**Proof.** The loop first checks whether $SP=0$. If not, it decrements $SP$ once and increments $T$ twice, then returns to the check. Thus each complete cycle consumes one unit of the original $SP$ and adds two units to $T$. After exactly the original $SP$ many cycles, the check exits with $SP=0$ and $T=T_0+2SP_0$. The bound hypothesis ensures that the increasing register never exceeds $B$: during the loop, $T$ is at most $T_0+2SP_0$, and every other register is either unchanged or the decreasing $SP$. The general doubling-loop execution theorem (`Complexity.LogProg.dmove_run`) packages this finite run and its guard; the componentwise register bounds supply its initial bound hypothesis (`Complexity.LogProg.SavitchARM.St.Bd.toV`). Identifying the two updated register coordinates with the stated record update gives the desired endpoint.

**Key facts.** `Complexity.LogProg.SavitchARM.St.Bd.toV`, `Complexity.LogProg.dmove_run`.
