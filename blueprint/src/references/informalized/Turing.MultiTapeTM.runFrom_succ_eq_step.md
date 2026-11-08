<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.runFrom_succ_eq_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run decomposition at the first step

**Claim.** The configuration after $t+1$ steps from $c$ is the configuration after $t$ steps starting from the one-step successor of $c$.

**Proof.** A run of length $t+1$ applies the step function $t+1$ times. Iterating first once and then $t$ more times gives the same result as iterating $t$ times from the one-step successor, by the composition law for function iteration.
