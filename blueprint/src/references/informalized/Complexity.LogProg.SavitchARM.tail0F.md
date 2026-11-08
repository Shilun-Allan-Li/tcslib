<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.tail0F -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phase-Zero Failure Loop

**Claim.** Under the stated invariant and bounds, the machine can pass from the phase-zero failure configuration to the loop configuration with $M$ increased by one, while every configuration before the endpoint satisfies the guard with bound $2^{w^2}$.

**Proof.** The invariant gives a register bound of $2^{w^2}$ (`Inv.bd`), and the elementary size estimate $2^w\le 2^{w^2}$ (`size_facts`) supports the required register bounds. From $a0F$, the machine clears $M$ and then transfers the old value of $V$ into $M$. This transfer is an instance of the bounded move routine `mv_run`: its source-plus-destination bound follows from the bounds on the registers. The resulting configuration has $M$ equal to the old value of $V$ and $V=0$. Prepending the instruction at $a0F$ with `step_of` gives reachability from the requested start. Next, the machine transfers $E$ into $V$, again using `mv_run`; here $E$ holds the original value of $V$. The transfer therefore restores $V$ and leaves $M$ unchanged. After identifying the resulting register vector with the one specified at the endpoint, the two runs compose by `AReach.trans`, yielding the desired loop configuration and guard bounds.

**Key facts.** `Complexity.LogProg.SavitchARM.size_facts`, `Complexity.LogProg.SavitchARM.Inv.bd`, `Complexity.LogProg.SavitchARM.step_of`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.reach_of_eq`, `Complexity.LogProg.AReach.trans`.
