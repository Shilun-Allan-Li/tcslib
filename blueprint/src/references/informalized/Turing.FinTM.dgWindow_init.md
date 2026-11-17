<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgWindow_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Computation Window

**Claim.** At time zero, the interval $[0,1)$ is a valid computation window: it has positive width, contains the heads, has blank cells outside it, is visited, satisfies the size bound, and contains the heads throughout the history up to time zero.

**Proof.** The window has width $1$, so it is positive and equals the allowed bound $2\cdot0+1$. The initial configuration puts every work head at coordinate $0$ and every tape cell is blank. Thus the heads lie in $[0,1)$, and every cell outside it is blank. Because there is at least one work tape, choose one of its heads; it visits coordinate $0$ at time zero, witnessing that the sole integer coordinate in the window is visited. Finally, the only time $u\le0$ is zero, so the same initial head-position calculation proves the history condition.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`.
