<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of trajectory recording

**Claim.** From the initial configuration, the recorder reaches completed control within $(T+1)(F(3T+4)+2T+7)$ steps, with the source configuration, recursively advanced counts, concatenated encoded rows, clock budget, logical time, and output as stated.

**Proof.** Use the prefix-recording result (`clRec_prefix`) at $j=T$. It reaches the row-ready control after at most $T(F(3T+4)+2T+7)$ steps, with source configuration equal to the machine’s configuration after $T$ steps, counts equal to the recursively advanced counts at time $T$, and record equal to the rows for times $0$ through $T-1$. The count bound (`clCounts_bound`) shows every count is at most $T$. The binary-width estimate (`clElapsed_width`) therefore bounds each count’s bit length by $T$, so the row-copy theorem (`clRec_copy`), used with width parameter $W=T$, applies. It appends the encoded row for the counts at time $T$ and reaches the clock-test control in at most $F(3T+4)+1$ additional steps, while preserving the source configuration and clock and time values. From that control, the stop transition (`clRec_stop`) enters completed control when the clock has reached its budget; it takes one further step. Concatenate these runs using `Turing.MultiTapeTM.runFrom_add` and the successor-run equation `runFrom_succ_eq_step'`. Adding the bounds gives the claimed total: $T A+(F(3T+4)+1)+1\le (T+1)A$, where $A=F(3T+4)+2T+7$.

**Key facts.** `Complexity.clRec_prefix`, `Complexity.clCounts_bound`, `Complexity.clElapsed_width`, `Complexity.clRec_copy`, `Complexity.clRec_stop`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
