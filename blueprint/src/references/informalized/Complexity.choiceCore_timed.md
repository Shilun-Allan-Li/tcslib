<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choiceCore_timed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Simulation-Core Behavior

**Claim.** After exactly $|u|+1$ steps, the core is halted and outputs $[1]$ exactly when the nondeterministic run from the given configuration under $u$ is halted with output $[1]$.

**Proof.** Apply the lockstep simulation (`Complexity.choiceCore_run`) for the full prefix length $|u|$. It identifies the core configuration after $|u|$ steps with the encoding of the nondeterministic configuration reached under all of $u$, together with a valid tag and choice-head position $|u|$. One further core step is the end-of-choice transition described by `Complexity.choiceCore_finish`: it halts and emits the Boolean verdict that the simulated configuration is halted and its output is $[1]$. The iterate successor identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies these two phases with the run of exactly $|u|+1$ steps.

**Key facts.** `Complexity.choiceCore_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.choiceCore_finish`.
