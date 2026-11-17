<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_table_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Table Rewind

**Claim.** For each $j\le |T|$, starting with the table cursor at $j-1$ in table-rewind control takes exactly $j+1$ steps to reach count-first control with the same flag and index and cursor zero.

**Proof.** Induct on $j$. At $j=0$, the cursor is $-1$, so the rewind transition sees a blank cell and moves right into count-first control at cursor zero. The one-step evaluation result (`Turing.timedCut_Eval_step`) and the zero-step and successor run laws (`Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_succ_eq_step`) establish this base case. For the successor case, the cursor is the natural position $j$. Since $j+1\le |T|$, this position is within the table, and the buffer-tape lookup fact (`Turing.FinTM.bufferTape_nat`) identifies the read symbol as the $j$th table bit. The rewind transition moves left and stays in rewind control. By `Turing.timedCut_Eval_step`, the cursor is now $j-1$, so the induction hypothesis applies and completes the remaining $j+1$ steps. Including the initial step gives $(j+1)+1$ steps, as claimed.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.timedCut_Eval_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
