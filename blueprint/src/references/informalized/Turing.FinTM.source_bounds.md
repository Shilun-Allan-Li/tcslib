<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Sweep.lean :: Turing.FinTM.source_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Bounds After a Computation

**Claim.** After $t$ steps from the initial configuration, every work-tape head lies in $[-t,t]$, and every cell strictly outside that interval is blank.

**Proof.** Induct on $t$. At time zero, all work-tape heads are at position zero and every cell is blank, so both bounds hold. For the successor step, each work-tape head moves by at most one: the step bound on head displacement gives $|p_{t+1}-p_t|\le1$ (`workTapePos_step_le`). Combining this with $-t\le p_t\le t$ places the next head in $[-(t+1),t+1]$. Now take a cell $z$ strictly outside this enlarged interval. It was already strictly outside $[-t,t]$, so it was blank by induction. It is also different from the old head position, since that position lies in $[-t,t]$. If the machine has halted, the tape is unchanged. Otherwise, a transition either leaves the tape unchanged or updates only the cell at the old head position; since $z$ is not that position, it remains blank. This proves both assertions at time $t+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.workTapePos_step_le`.
