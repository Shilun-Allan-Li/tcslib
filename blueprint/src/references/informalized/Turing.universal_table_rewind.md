<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_table_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Table Rewind

**Claim.** For every $j\le |T|$, starting in rewind phase with table cursor $j-1$ and running for $j+1$ steps yields count-parsing phase with table cursor zero, while preserving the flag, index, state tape, and state cursor.

**Proof.** Induct on $j$, retaining the bound $j\le |T|$. When $j=0$, the cursor is $-1$. The rewind transition at this position enters count-parsing phase and moves the table cursor right to zero; one-step evaluation and the zero-step run identity establish the claim. Now suppose the result holds for $j$ and consider $j+1$. The bound ensures that table position $j$ is within the list. Its tape read is the list entry $T[j]$, by the natural-position lookup rule (`bufferTape_nat`); the rewind transition moves left, remaining in rewind phase. Decomposing the run into this first step and the remaining run (`runFrom_succ_eq_step`), the new cursor is $(j+1)-1=j$. The induction hypothesis then rewinds the remaining $j+1$ steps to cursor zero and enters count-parsing phase. The zero-step identity (`runFrom_zero`) supplies the base run calculation.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_nat`, `Turing.universalEval_step`.
