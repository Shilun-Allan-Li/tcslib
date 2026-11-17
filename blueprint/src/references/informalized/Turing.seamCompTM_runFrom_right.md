<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamCompTM_runFrom_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run After the Handoff

**Claim.** After the first machine reaches its exit state for the first time, the composed run takes one handoff step and then follows the second machine’s run from the entry state.

**Proof.** First split the composed run at time $T_1+1$. Up to time $T_1$, the composed machine agrees with $M_1$ because the exit state has not occurred earlier (the left-run agreement theorem, `seamCompTM_runFrom_left`). At time $T_1$, the run is therefore at $c_1$ in the left component, by the assumed equality $M_1$’s run $=c_1$. Since $c_1$ is in the exit state, the next step switches to the entry state on the right while leaving the tapes unchanged (the handoff rule, `seamComp_dispatch`). The remaining $t$ steps agree with $M_2$’s run: its steps commute with placing states in the right component, so iterating that one-step agreement gives agreement for every $t$ (`runFrom_comm_of_step`). The run-splitting and successor identities (`runFrom_add` and `runFrom_succ_eq_step'`) express these phases as the stated total time $T_1+1+t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.seamCompTM_runFrom_left`, `Turing.seamComp_dispatch`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
