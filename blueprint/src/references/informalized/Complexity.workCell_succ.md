<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.workCell_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Work-Cell Update

**Claim.** After one step, cell $p$ on tape $\tau$ contains the symbol prescribed by the step when the head is at $p$; otherwise its contents are unchanged. In a halted configuration, the scanned symbol is retained.

**Proof.** The configuration after $t+1$ steps is the result of one transition from the configuration after $t$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step'`). Split according to whether that configuration is halted. If halted, the machine remains at the same configuration; consequently, the cell is unchanged, and the displayed conditional gives this same value whether or not $p$ is the head position. If the machine is active, applying its action updates the work tape at the current head position and leaves every other cell unchanged. The action's work-tape formula expresses this as a function update with the prescribed optional write, defaulting to the currently scanned symbol (`Turing.Action.apply_workTapes`). Evaluating that update at $p$ gives the prescribed symbol when $p$ is the head position and the old contents otherwise, as claimed.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.Action.apply_workTapes`.
