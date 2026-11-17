<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded completion of the row search

**Claim.** The matcher completes the search in at most $N\bigl(l(5W+7)+2W+5\bigr)+1$ steps, with the candidate bank, stream cursor, clock, and flags equal to the stated final values.

**Proof.** Apply the row-search prefix result (`Complexity.clMatch_prefix`) at $j=N$. It gives a time $t\le N\bigl(l(5W+7)+2W+5\bigr)$ at which the matcher is back in the clock-test control, has loaded the prior row for index $N$, has cursor at the length of the packed first $N$ rows, clock $N$, and has accumulated the comparison flags for rows $0$ through $N-1$. The prior-row convention makes the candidate bank empty when $N=0$ and row $N-1$ otherwise. One further step takes the clock-test control to the completed control without changing the tapes or their heads; this is precisely the stop-step identity (`Complexity.clMatch_stop`). The run-length successor identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) combines this step with the first $t$ steps, yielding time $t+1$ and the claimed bound.

**Key facts.** `Complexity.clMatch_prefix`, `Complexity.clMatch_stop`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
