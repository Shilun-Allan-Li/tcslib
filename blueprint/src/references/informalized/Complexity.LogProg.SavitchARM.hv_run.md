<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.hv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving Loop Execution

**Claim.** From any state whose eighteen registers are at most $B$, the halving loop reaches the pop routine's copy-loop state. It sets the counter to zero, replaces the temporary register by its initial value divided by $2$ raised to the initial counter, leaves the other registers unchanged, and satisfies the guard before the final configuration.

**Proof.** At each iteration, the loop checks whether the counter is zero. If it is positive, it decrements the counter and halves the temporary register, then returns to the check. After the initial counter value $C_0$ iterations, the counter is zero and the temporary register has been halved $C_0$ times, hence equals $T_0/2^{C_0}$. No other register changes. The halving-loop execution theorem supplies this finite guarded run (`Complexity.LogProg.halve_run`); the initial coordinate bounds required by that theorem follow from the state bounds (`Complexity.LogProg.SavitchARM.St.Bd.toV`). The theorem's two register updates are exactly the stated state update.

**Key facts.** `Complexity.LogProg.SavitchARM.St.Bd.toV`, `Complexity.LogProg.halve_run`.
