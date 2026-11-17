<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_borrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Borrow Operation

**Claim.** Starting in controller phase eight with counter word $w$ at head zero, the host completes the borrow operation in $2j+2$ steps, where $j$ is the length of the initial run of false bits. It ends with the decremented word, head at zero, and control at the next-anchor call on success or phase eleven on underflow; moreover $2j+2\le 2|w|+2$.

**Proof.** The bound follows from the fact that the initial false-run length is at most the word length (`loopBorrowPos_le`). For the run equality, first use the borrow-run description (`loopHost_borrow_run`) with empty prefix: after $j+1$ steps the host has scanned the initial false bits, and the counter is positioned for the corresponding rewind phase. The output word of the debit has the same length as $w$ (`loopDebit_length`), so the rewind estimate applies. Split the total time $2j+2$ into these two segments using the run-addition law (`runFrom_add`), then apply the borrow-rewind description (`loopHost_borrow_rewind`). It returns the head to zero and places the control at the next-anchor call exactly when the debit succeeds, or at phase eleven when it underflows, with the decremented word on the counter track.

**Key facts.** `Turing.FinTM.loopBorrowPos_le`, `Turing.FinTM.loopHost_borrow_run`, `Turing.FinTM.loopDebit_length`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.loopHost_borrow_rewind`.
