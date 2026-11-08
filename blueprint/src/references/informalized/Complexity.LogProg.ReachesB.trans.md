<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.ReachesB.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of bounded reaching

**Claim.** If $c_0$ reaches $c_1$ and $c_1$ reaches $c_2$ with the register head bounded between $-1$ and $L$ at every intermediate time, then $c_0$ reaches $c_2$ with the same bound relative to $c,r$.

**Proof.** Take witnessing times $T_1,T_2$ for the two bounded-reaching relations and use $T_1+T_2$ as the combined time. The run-composition identity (\texttt{rrun_add}) gives the endpoint $c_2$. For each intermediate time before $T_1$, the first witness supplies a state, input-head position, and register-head position satisfying the required reference form, no-call condition, and bounds. For a time at least $T_1$, write it as $T_1+t'$; composition identifies its configuration with the run from $c_1$ at time $t'$, and $t'<T_2$, so the second witness supplies all those same conditions.

**Key facts.** `Complexity.LogProg.rrun_add`.
