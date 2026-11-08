<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wr_timeout_dispatch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timeout dispatch after the first hit

**Claim.** If the run of $H$ first reaches a timeout state at time $t$, then after $t+1$ steps the timeout runner is at the configuration of $H$ at time $t$, with its state replaced by the halted runner phase.

**Proof.** Use the phase-host run theorem, which describes both the simulation before a redirection and the transition at the first redirected state ($\texttt{Turing.phaseHostTM\_run}$). Take the active phase to simulate $H$, and use the given time-$t$ configuration as the endpoint. The hypothesis that its state is $\mathrm{timeout}(r)$ makes the redirection rule fire there, sending the runner to the halted phase. At every earlier time, the first-hit hypothesis rules out every timeout state, so the redirection rule returns no successor and the host follows $H$ exactly. The phase-host theorem therefore gives the stated configuration after one further dispatch step.

**Key facts.** `Turing.phaseHostTM_run`.
