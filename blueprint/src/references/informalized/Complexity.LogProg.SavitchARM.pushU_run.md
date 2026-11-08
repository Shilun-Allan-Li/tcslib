<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.pushU_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Endpoint Push

**Claim.** Under the stated register bounds and zero conditions, the phase-true push routine saves $U$ on the endpoint stack, doubles the phase stack, and reaches the push-increment instruction with $U=0$, without recording an answer. Every visited configuration satisfies the program precondition and register bound.

**Proof.** The routine first copies the code width $w$ into the loop counter. Shifting the endpoint stack by this count multiplies $SE$ by $2^w$. The hypothesis $SE\,2^w+U\le B$ bounds the resulting stack together with the source endpoint, and the initial register bounds supply the remaining conditions for the copy and shift routines. The copy routine then transfers $U$ into the shifted stack and clears $U$, so the stack is $SE\,2^w+U$. Next, the doubling routine replaces its scratch value by $T+2SP=2SP$, since initially $T=0$. A final move transfers this value to the phase stack and clears the scratch register. Because this is the phase-true case, the move exits at the push-increment instruction. The copy, shift, doubling, and move reachability results each preserve the guard along their execution; composing them gives the claimed run and its guard.

**Key facts.** `Complexity.LogProg.SavitchARM.cp_run`, `Complexity.LogProg.SavitchARM.sh_run`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.SavitchARM.dm_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
