<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean :: Complexity.LogProg.arm_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled program space bound

**Claim.** Under the stated halting, precondition, and register-length assumptions, the compiled machine halts with output $b$ and uses at most $m(W+2)+k_D(2B+1)$ space.

**Proof.** Apply the halting simulation theorem (`arm_run`) to the run from the initial state with all registers zero and empty output. It gives a time $T$ at which the compiled run halts with output $[b]$, bounds every register-tape head between $-1$ and $W$, and provides the invariant at all earlier tape times. The encoding of this initial register configuration is the compiled machine's initial configuration (`init_eq_aseam`). Thus the hypotheses of the general compiled-machine space theorem (`compile_space`) hold through time $T$: the head bounds hold at earlier times by the invariant, at time $T$ by the endpoint bound from `arm_run`, and the call condition holds at all times before $T$. That theorem yields a halting time and bounds space using the register tapes and the simulated decider tapes. Each of the $m$ register tapes contributes at most $W+2$ visited cells, since its head lies in the integer interval from $-1$ through $W$; each of the $k_D$ decider tapes contributes at most $2B+1$ cells, since its head positions lie between $-B$ and $B$. Summing these contributions gives the stated bound.

**Key facts.** `Complexity.LogProg.arm_run`, `Complexity.LogProg.init_eq_aseam`, `Complexity.LogProg.compile_space`.
