<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_track_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape support lies within the visited span

**Claim.** Any cell outside the interval between the leftmost and rightmost head positions visited through time $t$ is blank after $t$ steps.

**Proof.** Induct on $t$. Initially the work tape is blank everywhere. For the successor step, a cell outside the new interval is also outside the old interval: the new bounds are obtained by taking the minimum and maximum with the new head position. The visited-interval bounds place the old head within the old interval, so the outside cell is not the old head position. The next configuration is one step after the old one (`runFrom_succ_eq_step'`). If the machine is halted, its tape is unchanged. If it is active, the transition either leaves the tape unchanged or updates it only at the old head position, by the definition of applying an action. Since the cell under consideration is not that position, its contents remain the old contents. The induction hypothesis therefore says it is blank.

**Key facts.** `Turing.FinTM.emCall_track_extent`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
