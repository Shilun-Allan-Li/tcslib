<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_initial_skip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping the Initial State Field

**Claim.** If the table has $n$ consecutive true symbols followed by false at the cursor, then the initial-state-skipping phase advances past those $n+1$ symbols and enters the record-group selection phase with the same index.

**Proof.** Induct on $n$, generalizing the prefix $l$. When $n=0$, the next table symbol is false, by `timedCut_table_read`. The interpreter therefore moves directly from initial-skip to group and advances the cursor once, as specified by `timedCut_Eval_step`; the zero- and successor-run laws express this one-step run. For the successor case, the next symbol is true. The table-reading fact and interpreter-step fact show that one step remains in initial-skip and advances the cursor. The remaining table has $n$ true symbols and then false, now with prefix $l++[true]$, so the induction hypothesis applies. The successor-run law composes the first step with that remaining run, and list-length arithmetic gives the claimed final cursor.

**Key facts.** `Turing.timedCut_table_read`, `Turing.timedCut_Eval_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
