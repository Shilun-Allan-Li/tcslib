<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.snapshotAt_state_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor State of a Run

**Claim.** The state in the snapshot after $t+1$ steps is the state prescribed by one transition from the snapshot at time $t$, with a halted state remaining halted.

**Proof.** Split according to whether the configuration at time $t$ has a state. The run-after-one-more-step identity says that the configuration at time $t+1$ is obtained by applying one machine step to the time-$t$ configuration. If its state is absent, the step leaves the configuration unchanged, so the next snapshot's state is absent, as required by the definition of the snapshot state update. If its state is present, the step applies the transition determined by that state and the scanned symbols; the resulting configuration's state is exactly the successor-state component of that transition. In both cases this is the state update specified by the snapshot rule.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
