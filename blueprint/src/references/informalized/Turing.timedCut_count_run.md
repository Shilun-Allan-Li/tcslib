<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_count_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping a Doubled Count Field

**Claim.** When the table contains the doubled bits of $b$, followed by the delimiter $01$, the count-first phase advances past that field in $2|b|+2$ steps, arriving at the stated initial-copy or initial-skip phase and cursor.

**Proof.** Proceed by induction on the word $b$, generalizing the prefix $l$. If $b$ is empty, the table begins at the cursor with the delimiter $01$. The table-reading fact (`timedCut_table_read`) identifies the next two symbols as false and true; the interpreter-step fact (`timedCut_Eval_step`) then shows that these two reads move from count-first to count-second and then to the specified terminal phase, advancing the cursor twice. For a nonempty word $b_0::b$, the first two table symbols are both $b_0$. The same table-reading and interpreter-step facts show that two steps return the interpreter to count-first with the cursor advanced by two. The remaining table has the same required form, with prefix $l++[b_0,b_0]$, so the induction hypothesis processes it in $2|b|+2$ further steps. The run-composition laws (`runFrom_add`, with the successor and zero run laws `runFrom_succ_eq_step'` and `runFrom_zero`) join these initial two steps to the remaining run. The cursor and total-time expressions agree because the consumed prefix has length two.

**Key facts.** `Turing.timedCut_table_read`, `Turing.timedCut_Eval_step`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`.
