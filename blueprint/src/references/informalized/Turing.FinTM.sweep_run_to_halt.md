<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweep_run_to_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Through the First Halt

**Claim.** If the source machine is nonhalting at every time before $\tau$, then at each time $t\leq\tau$ the single-tape simulator has completed the prescribed number of steps and is in the canonical configuration representing the source configuration at time $t$, with the stated zone and work-head coordinate.

**Proof.** Induct on $t$. At $t=0$, the initialization identity (`sweep_init`) gives the simulator's initial canonical configuration with the stated zone and frontier. For the successor case, the hypothesis $t+1\leq\tau$ ensures that the source configuration at time $t$ is nonhalting. Hence it has some state $q$. The source bounds (`source_bounds`) place every work head at or to the right of $-t$, and strictly before the right endpoint $-t+(2t+1)$; the same bounds show that all tapes are blank immediately outside this zone. These are precisely the hypotheses needed for one simulated step (`sweep_step`).

Split the simulator's time at the completed time for $t$, using additivity of runs (`runFrom_add`) and the induction hypothesis. Apply `sweep_step` to advance from the canonical configuration at time $t$ to the one for the source successor. Its duration agrees with the increment in `sweepTime` after the integer identity $(2(2t+1)+5)k+4=(4t+7)k+4$. The successor zone begins at $-(t+1)$, has size $2(t+1)+1$, and its frontier is $-(t+1)k-1$, by the displayed arithmetic. The run-successor identity (`runFrom_succ_eq_step'`) identifies the source configuration after one further step with the required time-$t+1$ configuration.

**Key facts.** `Turing.FinTM.sweep_init`, `Turing.FinTM.source_bounds`, `Turing.FinTM.sweep_step`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
