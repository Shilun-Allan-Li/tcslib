<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.tail1T -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase-One Success Return

**Claim.** Under the stated invariant, the machine can move from the phase-one success configuration to the successful return state, restoring $U$ to its original value and retaining $M=M_2$, with all registers before the endpoint bounded by $2^{w^2}$.

**Proof.** The invariant bounds every register by $2^{w^2}$ (`Inv.bd`), and $2^w\le 2^{w^2}$ (`size_facts`) provides the needed comparison. At $a1T$, the machine clears $U$ and then transfers $E$ into $U$. Since $E$ stores the original value of $U$, this restores $U$. The bounded move routine `mv_run` gives the transfer and its guard bounds; the endpoint register vector is the stipulated one, as `reach_of_eq` records. Finally, `step_of` prepends the instruction from $a1T$ to that move run, giving the claimed reachability.

**Key facts.** `Complexity.LogProg.SavitchARM.size_facts`, `Complexity.LogProg.SavitchARM.Inv.bd`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.reach_of_eq`, `Complexity.LogProg.SavitchARM.step_of`.
