<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.correct_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness Advances by One Step

**Claim.** If all local checks pass, the table correctly describes the machine at time $t$, and $t+1<2^W$, then it correctly describes the machine at time $t+1$ in the same three senses.

**Proof.** Let $c$ be the machine configuration at time $t$. The next-time state and output claim is proved directly from the local state-transition check at address zero. The current claims identify the proposed current state and read symbols with $c$ and its actual reads (`claims_of_correct`). Since the time guard holds, the check forces the next state-and-output answer to be the transition-rule result. The run at time $t+1$ is one step from $c$ (`runFrom_succ_eq_step`), and its state/output summary is precisely that transition-rule result (`SS_step`). The work-tape and input-symbol parts of correctness at time $t+1$ follow from the corresponding preservation results `work_correct` and `input_correct`, which apply the local tape checks together with the time-$t$ correctness hypothesis.

**Key facts.** `Complexity.Meyer.claims_of_correct`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.Meyer.SS_step`, `Complexity.Meyer.work_correct`, `Complexity.Meyer.input_correct`.
