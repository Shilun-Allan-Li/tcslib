<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundTM_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Redirected Phases Form Round Spans

**Claim.** If a phase machine runs from $d$ to $e$ in $T$ steps under the stated no-earlier-redirection and round-window hypotheses, then the full round machine runs from the configuration embedded under the phase label to the redirected endpoint in $T+1$ steps, and this run satisfies the round-span property.

**Proof.** The phase-host simulation result `phaseHostTM_run` describes the full machine during the phase: through time $T$ it agrees with the phase machine run, embedded under the fixed phase label, and one additional step performs the specified redirection. This gives the endpoint and the claimed total time. For each earlier time $u<T+1$, the phase run is still live: if it had halted at $u$, `runFrom_add` and `runFrom_of_halt` would make it remain at that halted configuration through time $T$, contradicting the live state of its endpoint. Thus its state can be written as some phase state $q$, and the embedded state has label `key`. Since `key` is neither entry nor halt, the embedded state is neither distinguished endpoint state. The round-window property at time $u$ is exactly the assumed window property for the phase run.

**Key facts.** `Turing.phaseHostTM_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
