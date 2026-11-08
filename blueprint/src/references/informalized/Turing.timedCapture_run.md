<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCapture_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep Capture Run

**Claim.** If the original machine does not halt before time $t$, then after $t$ steps the capture machine started from the embedded configuration is exactly the embedding of the original machine's time-$t$ configuration.

**Proof.** Proceed by induction on $t$. At time zero, both sides are the same embedded starting configuration. For the successor step, the hypothesis that the original run has not halted at any time before $t+1$ implies in particular that its configuration at time $t$ has a present state. By the induction hypothesis, the capture machine at time $t$ is the embedding of that configuration. The one-step correspondence for a configuration with a present state (`timedCapture_step`) says that advancing the capture machine once gives the embedding of the original machine's next configuration. Rewriting both runs at time $t+1$ as one step after their time-$t$ configurations (`MultiTapeTM.runFrom_succ_eq_step'`) completes the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedCapture_step`.
