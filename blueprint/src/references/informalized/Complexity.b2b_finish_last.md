<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_finish_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Test and Head Bound

**Claim.** Under the identity-machine and cleaned-simulation hypotheses, the host started in its final-test configuration halts with output $[b]$ in finite time, and every work-tape head stays within distance $|x|+|u|+s_v+s_i+1$ of zero throughout the run.

**Proof.** Let $K$ be the number of work tapes used by the test machine, and view that test machine as embedded into the host’s tapes. The trial-run result (`b2b_trial_run`) supplies a time $T$ at which the test has reached its verdict state carrying $b$, with the stored word $x\mathbin{++}u$ and the required head bounds throughout the trial. The embedding preserves the simulated run (`embedEmitTM_runFrom`), so the embedded test reaches the corresponding configuration at time $T$. The phase-host run principle (`phaseHostTM_run`) then shows that the host executes this final-test phase through time $T$ and takes its prescribed transition to the answer phase; its guard hypothesis follows because the trial’s earlier configurations do not already have a completed verdict. The state retagging needed to identify these configurations is exactly `b2b_dispatch_retag`. At the boundary configuration, `b2b_finish_answer` shows that two further steps halt and append the single output symbol $b$.

For the head bound during the embedded test, each simulated tape retains the position of its corresponding test tape, by `embedEmitCfg_selected_pos`, so the trial’s head bound applies. The one extra host tape is outside the embedding; `embedEmitTM_frame` says its head remains at its initial position zero. Thus every head has the stated bound through time $T$. In particular the final answer configuration has that bound. After the phase transition, the two answer-phase steps preserve all head positions, again by `b2b_finish_answer`; hence the same bound holds through halting. Combining the trial and answer portions gives the required finite halting time and output.

**Key facts.** `Complexity.b2b_trial_run`, `Turing.embedEmitTM_runFrom`, `Turing.phaseHostTM_run`, `Complexity.b2b_dispatch_retag`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`, `Complexity.b2b_finish_answer`.
