<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.sim_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Run Simulation

**Claim.** For any $t$ and state $s$ with read position at most $|x|$ and every register value plus $t$ at most $B$, the compiled machine reaches the encoding of the state after $t$ program steps in at most $t(2B+3)$ machine steps.

**Proof.** Proceed by induction on $t$. For $t=0$, both runs leave their initial configurations unchanged, so zero machine steps suffice. If the abstract state is already halted, its program run remains unchanged, and again zero machine steps suffice. Otherwise, apply the one-step simulation result (`sim_step`) to reach the encoding of the state after one abstract step in at most $2B+3$ machine steps. The bound on each register ensures the current register values are at most $B$. The next state still has read position at most $|x|$ (`step_pos_le`), and its registers are bounded by the previous values plus one (`step_regs_le`). Thus the induction hypothesis simulates the remaining $t$ abstract steps, with each register value plus $t$ bounded by $B$. Concatenating the two machine runs using the run-addition law (`Turing.MultiTapeTM.runFrom_add`) gives a run to the encoding after $t+1$ steps. The two time bounds add to $(2B+3)+t(2B+3)=(t+1)(2B+3)$.

**Key facts.** `Complexity.CounterProg.run_of_halted`, `Complexity.CounterProg.sim_step`, `Complexity.CounterProg.step_pos_le`, `Complexity.CounterProg.step_regs_le`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.CounterProg.run_succ`.
