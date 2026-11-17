<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.phaseHostTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs of a Phase-Hosted Machine

**Claim.** Under the stated endpoint and state-avoidance hypotheses, the phase-hosted machine follows the tagged run of $M_i$ through time $T$, and at time $T+1$ reaches the endpoint configuration with its state replaced by $q'$.

**Proof.** For each time $u\le T$, the hypothesis on the run of $M_i$ ensures that every state encountered before time $u$ is one where the reduction rule returns no successor. On precisely those states, the phase-hosted machine uses the transition of $M_i$, with its state tagged by $i$. The run-agreement theorem (\(\texttt{Turing.MultiTapeTM.runFrom_mapState_of_agreeOn}\)) therefore identifies the two runs, after tagging, at every time through $T$. For the next step, the run at time $T$ is $c'$ by the given endpoint equality, and its state is $s'$. After tagging, the reduction rule at that state returns $q'$, so the host takes its reduction transition. This transition leaves the non-state parts of the configuration unchanged and sets the state to $q'$, giving the claimed configuration at time $T+1$. The one-step run identity (\(\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step'}\)) connects this transition to the run at time $T+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
