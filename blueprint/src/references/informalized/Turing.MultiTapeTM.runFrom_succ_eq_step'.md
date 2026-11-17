<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.runFrom_succ_eq_step' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run decomposition at the last step

**Claim.** The configuration after $t+1$ steps from $c$ is obtained by taking one step from the configuration after $t$ steps from $c$.

**Proof.** A run of length $t+1$ applies the step function $t$ times and then once more. This is precisely the composition law for iterating a function, with the final application being the step from the configuration reached at time $t$.
