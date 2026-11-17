<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.sim_run_of_regs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Under Register Bounds

**Claim.** If the read position of $s$ is at most $|x|$ and every register remains at most $B$ at each of the first $t$ abstract times, then the compiled machine reaches the encoding of the state after $t$ steps in at most $t(2B+5)$ machine steps.

**Proof.** Induct on $t$, generalizing the initial state. For $t=0$, both runs take zero steps. For the successor case, first simulate one abstract step using the bounded-run simulation theorem (`sim_run`) with register allowance $B+1$ and one abstract step. The initial registers are at most $B$ by the hypothesis at time zero, so this costs at most $2(B+1)+3=2B+5$ machine steps. The intermediate state has read position at most $|x|$ by preservation of the input bound (`step_pos_le`). Apply the induction hypothesis to this intermediate state for the remaining $t$ steps: the assumed register bounds transfer to it because its time-$j$ state is the original run's time-$1+j$ state, by the run-addition law (`run_add`). Concatenate the machine runs with `Turing.MultiTapeTM.runFrom_add`; their total cost is at most $(2B+5)+t(2B+5)=(t+1)(2B+5)$. The run-zero and run-succ identities (`run_zero`, `run_succ`) identify the abstract endpoint with the required state after $t+1$ steps.

**Key facts.** `Complexity.CounterProg.run_zero`, `Complexity.CounterProg.sim_run`, `Complexity.CounterProg.step_pos_le`, `Complexity.CounterProg.run_add`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.CounterProg.run_succ`.
