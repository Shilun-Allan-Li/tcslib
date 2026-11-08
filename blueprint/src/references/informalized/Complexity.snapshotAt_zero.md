<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.snapshotAt_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Snapshot

**Claim.** At time zero, the snapshot consists of the initial state, the input symbol at position $1$ (blank if the input is empty), and blank under every work-tape head.

**Proof.** At the initial configuration the input head is at position $1$. The input-symbol-at-position lemma therefore identifies the scanned symbol with the first list entry, interpreted as blank when that entry does not exist. The run at time zero is the initial configuration itself. Its state is the initial state, and every work-tape cell is blank, so the symbol under each initial work head is blank as well.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.MultiTapeTM.runFrom_zero`.
