<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_runFrom_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Run on the First Machine's Side

**Claim.** If the first machine avoids the exit state at every time before $T$, then through every time $t\le T$ the composed machine's run from the left-state version of $c$ agrees exactly with the first machine's run, with its state placed in the left component.

**Proof.** Proceed by induction on $t$. At time zero, both runs start from the same configuration after mapping its state into the left component. For the successor step, write each run at time $t+1$ as one machine step applied to its time-$t$ configuration (`MultiTapeTM.runFrom_succ_eq_step'`). The induction hypothesis identifies those time-$t$ configurations. Since $t<T$, the first machine's configuration then does not have the exit state, so the composed machine's step on this left-state configuration agrees with the first machine's step, with the resulting state still mapped left (`seamComp_step_left`). Applying the run-step identity again establishes the required equality at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.seamComp_step_left`.
