<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_borrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Host borrow operation

**Claim.** The borrow operation reaches its specified post-borrow frame after $2b(w)+2$ steps, and this time is at most $2|w|+2$.

**Proof.** The bound follows from $b(w)\le |w|$, the borrow-position estimate (`f2_loopBorrowPos_le`), followed by multiplying by two and adding two. For the configuration, first apply the borrow-run identity (`f2_loopHost_borrow_run`) with empty prefix: after $b(w)+1$ steps the counter contains the debited word and the machine is in the appropriate rewind phase, 9 for a carry and 10 otherwise. The debit preserves word length (`f2_loopDebit_length`), so the rewind lemma applies to that entire word. It takes another $b(w)+1$ steps to restore the counter head to zero and reach the stated return call or phase 11. Splitting the total run into these two equal-length segments uses the run concatenation identity (`runFrom_add`).

**Key facts.** `Turing.FinTM.f2_loopBorrowPos_le`, `Turing.FinTM.f2_loopHost_borrow_run`, `Turing.FinTM.f2_loopDebit_length`, `Turing.FinTM.f2_loopHost_borrow_rewind`, `Turing.MultiTapeTM.runFrom_add`.
