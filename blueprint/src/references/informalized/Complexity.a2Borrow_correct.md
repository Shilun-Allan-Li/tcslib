<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Borrow_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Decrement Round

**Claim.** For every output word, input word $x$, valid input-head position $p$, and binary word $u$, the round takes at most $2|u|+2$ steps and, after exactly $2\beta(u)+2$ steps, reaches the configuration with head at cell zero, counter the fixed-width decrement of $u$, and the associated success flag.

**Proof.** First, the borrow-position bound gives $2\beta(u)+2\le 2|u|+2$. To identify the resulting configuration, split the run into two phases, each of length $\beta(u)+1$. The borrow-scan computation (`a2Borrow_run`), with empty prefix, shows that the first phase reaches the borrow-result state carrying the decrement's success flag; the head is at $\beta(u)-1$, and the tape contains the decremented word. The empty-prefix specialization removes the prefix from the tape and places the head at that indicated position. The run-addition law (`Turing.MultiTapeTM.runFrom_add`) composes this phase with the rewind phase. Since the decremented word has the same length as $u$ (`a2Debit_length`), the borrow-position bound ensures the rewind lemma applies; it returns the head to zero without changing the tape and enters the state carrying the success flag. The input position and output are unchanged in both phases, so the final configuration is the one asserted.

**Key facts.** `Complexity.a2BorrowPos_le`, `Complexity.a2Borrow_run`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.a2Debit_length`, `Complexity.a2Borrow_rewind`.
