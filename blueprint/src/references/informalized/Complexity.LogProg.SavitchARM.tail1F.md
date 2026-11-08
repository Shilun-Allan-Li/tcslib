<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.tail1F -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase-One Failure Loop

**Claim.** Under the stated invariant and bounds, the machine can pass from the phase-one failure configuration to the loop configuration with $M$ increased by one, while every configuration before the endpoint satisfies the guard with bound $2^{w^2}$.

**Proof.** The invariant supplies the register bound $2^{w^2}$ (`Inv.bd`), while $2^w\le 2^{w^2}$ (`size_facts`) supplies the corresponding numerical comparison. At $a1F$, the machine clears $M$, then transfers the old value of $U$ into $M$; the bounded move routine `mv_run` realizes this transfer. The result has $M$ equal to the original $U$ and $U=0$. The initial instruction is prepended using `step_of`. The next move transfers $E$, which holds the original $U$, back into $U`, leaving $M$ fixed. `mv_run` supplies this bounded transfer as well. The register vector of the resulting configuration is the specified endpoint vector, so `reach_of_eq` identifies them; composing the two runs with `AReach.trans` proves the claim and preserves the guard along the run.

**Key facts.** `Complexity.LogProg.SavitchARM.size_facts`, `Complexity.LogProg.SavitchARM.Inv.bd`, `Complexity.LogProg.SavitchARM.step_of`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.reach_of_eq`, `Complexity.LogProg.AReach.trans`.
