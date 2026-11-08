<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_model_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Phases before the read model exits

**Claim.** If the read model is in its exit state carrying $a$ after $T$ steps, then at every earlier time $n<T$ its state is a read phase.

**Proof.** The read model's run agrees at every time with the run of its underlying multi-tape machine (`read_run_eq`). Since the machine has a non-none state at time $T$, it cannot have reached a none state at any earlier time: once a run has halted, all subsequent states remain none (`runFrom_state_ne_none_of_le`). Now fix $n<T$. The state at time $n$ is therefore some label. If it is a read phase, the conclusion follows. If it is an exit label, the next transition uses the exit state's junk action, which halts; hence the state at time $n+1$ is none (`runFrom_succ_eq_step'`). This contradicts the fact that the machine's state remains non-none through time $T$. Thus every earlier state is a read phase.

**Key facts.** `Complexity.LogProg.read_run_eq`, `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
