<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wr_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement before a timeout

**Claim.** If the run of $H$ avoids every timeout state at all times strictly before $t$, then the runner in its active mode agrees with $H$ through every time $u\le t$, including the state tagged as active.

**Proof.** Apply the run-agreement principle for a host machine that simulates a source machine on states satisfying a guard ($\texttt{Turing.MultiTapeTM.runFrom\_mapState\_of\_agreeOn}$). Here the embedding tags each source state with the active flag, and the guard says that the state is not any timeout state. On a guarded state, the runner's redirection rule has no successor, so its transition is exactly the transition of $H$ with the state mapped through the embedding. For every time strictly before $u$, the assumed avoidance through times strictly before $t$, together with $u\le t$, supplies this guard. The run-agreement principle therefore gives equality at time $u$, including the state tag.

**Key facts.** `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`.
