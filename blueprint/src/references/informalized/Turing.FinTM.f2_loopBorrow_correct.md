<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBorrow_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Borrow Computation

**Claim.** The prescribed time $2b+2$, where $b$ is the initial false-segment length of $u$, is bounded by $2|u|+2$, and the debit machine reaches its result configuration at that time.

**Proof.** The time bound follows from the bound on the initial false segment, $b\le |u|$ (`f2_loopBorrowPos_le`). To identify the configuration at the stated time, write $2b+2=(b+1)+(b+1)$. The borrow-run result (`f2_loopBorrow_run`), with empty prefix, shows that after the first $b+1$ steps the machine is in the borrow-result state, with the computed Boolean outcome and the modified word on its tape. The modified word has the same length as $u$ (`f2_loopDebit_length`), so the bound needed to rewind from this position is still $b\le |u|$. The rewind result (`f2_loopBorrow_rewind`) then shows that the next $b+1$ steps return the head to zero, preserve that word and outcome, and enter the terminal result state. The run-addition law (`runFrom_add`) combines these two portions of the computation.

**Key facts.** `Turing.FinTM.f2_loopBorrowPos_le`, `Turing.FinTM.f2_loopBorrow_run`, `Turing.FinTM.f2_loopDebit_length`, `Turing.FinTM.f2_loopBorrow_rewind`, `Turing.MultiTapeTM.runFrom_add`.
