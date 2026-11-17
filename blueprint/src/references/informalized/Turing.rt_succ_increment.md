<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_succ_increment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment Phase Handoff

**Claim.** If the increment machine reaches a completed phase with flag $b$ at time $t$, and no earlier configuration is completed, then the successor machine agrees with the embedded increment run through time $t$. At time $t+1$, its state is the exit phase when $b$ is true and the extension phase’s initial state when $b$ is false.

**Proof.** View the successor machine as a host that runs the increment machine in its increment phase and redirects only at designated completed states. The phase-host run theorem (`Turing.phaseHostTM_run`) applies to this run. Before time $t$, the guard holds because the hypothesis excludes every completed increment state; thus no redirect occurs, and the host run agrees with the increment run under the state embedding at every time through $t$. At time $t$, the state is the completed state with flag $b$. The host’s redirect sends a true flag to the exit phase and a false flag to the extension phase’s initial state. The theorem therefore gives the asserted configuration at the next step.

**Key facts.** `Turing.phaseHostTM_run`.
