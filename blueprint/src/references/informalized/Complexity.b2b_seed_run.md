<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_seed_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeded Counter Initialization

**Claim.** Starting in the host machine’s counter phase with $Q$ true bits on the word tape, after $(2Q+3)+(2Q+3)$ steps the machine is in its rewind-start state with $Q$ false bits on that tape and $Q$ true bits on the buffer tape. At every time up to then, each work-tape head is at distance at most $Q+1$ from the origin.

**Proof.** Write $w$ for the word of $Q$ true bits, let $U$ be the designated word tape, and let $C$ be the counter tape. First the counter phase copies $w$ from $U$ to $C$. The copy-machine run result says that a forward sweep copies the word and a return sweep restores the heads, taking $2|w|+2=2Q+2$ steps; its intermediate configurations keep the heads within the interval from $-1$ to $Q$ (`Turing.copyTM_run_ofCfg`). Since $U$ and $C$ are distinct, the resulting configuration has $w$ on both tapes and the host dispatches to the zeroing phase.

The zeroing phase increments the word on $U$. An all-true word is the overflow case: incrementing it leaves $Q$ false bits and returns the head to the origin in another $2Q+2$ steps. The overflow-run result also bounds the head positions at every intermediate time (`Turing.incrementTM_run_overflow_ofCfg`). Consequently the two sweeps together take $(2Q+2+1)+(2Q+2+1)$ steps, where each additional step is the host’s phase dispatch. The phase-host run theorem justifies following each phase’s run through its dispatch, and the dispatch-retag identity identifies the resulting host configurations (`Turing.phaseHostTM_run`, `Complexity.b2b_dispatch_retag`). The word-tape and counter-tape sweeps stay between $-1$ and $Q$; all other work-tape heads remain at the origin. Thus every head has absolute position at most $Q+1$, and after the second dispatch the host is in the rewind-start state with the required tape contents. The run-composition law combines the two phase durations (`Turing.MultiTapeTM.runFrom_add`).

**Key facts.** `Turing.copyTM_run_ofCfg`, `Turing.incrementTM_run_overflow_ofCfg`, `Turing.phaseHostTM_run`, `Complexity.b2b_dispatch_retag`, `Turing.MultiTapeTM.runFrom_add`.
