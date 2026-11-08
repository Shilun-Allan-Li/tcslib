<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.pushV_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Endpoint Push

**Claim.** Under the stated register bounds and zero conditions, the phase-false push routine saves $V$ on the endpoint stack, doubles the phase stack, and reaches the move routine that transfers the midpoint into $V$, with $V=0$ and no answer recorded. Every visited configuration satisfies the program precondition and register bound.

**Proof.** The routine first copies the code width $w$ into the loop counter. Shifting the endpoint stack by this count multiplies $SE$ by $2^w$. The hypothesis $SE\,2^w+V\le B$ bounds the resulting stack together with the source endpoint, and the initial register bounds supply the remaining conditions for the copy and shift routines. The copy routine then transfers $V$ into the shifted stack and clears $V$, leaving $SE\,2^w+V$. The doubling routine changes its scratch value to $T+2SP=2SP$, since initially $T=0$. A final move transfers this value to the phase stack and clears the scratch register. In the phase-false case the move exits at the instruction that transfers the midpoint into $V$. Each routine's reachability result ensures the guard throughout its execution; composing those runs and identifying the final register configuration gives the claim.

**Key facts.** `Complexity.LogProg.SavitchARM.cp_run`, `Complexity.LogProg.SavitchARM.sh_run`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.SavitchARM.dm_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
