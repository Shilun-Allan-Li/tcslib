<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating reachability and halting

**Claim.** If the machine reaches $b$ from $a$ with invariant $G$ holding strictly before reaching $b$, and then halts from $b$ with answer $r$ while $G$ holds strictly before halting, it halts from $a$ with answer $r$ and with $G$ holding strictly before that halt.

**Proof.** Let $T_1$ be the time to reach $b$ and $T_2$ the time to halt from $b$. The run-addition identity (\texttt{Complexity.LogProg.mrun_add}) says that running for $T_1+T_2$ steps from $a$ is the same as first running $T_1$ steps to $b$ and then running $T_2$ more. Thus the halted state and answer at time $T_1+T_2$ are exactly those supplied by the halting run from $b$. For the invariant, take any $t<T_1+T_2$. If $t<T_1$, the reachability hypothesis gives $G$ at time $t$. Otherwise write $t=T_1+t'$; then $t'<T_2$, and the run-addition identity identifies the configuration at time $t$ with the configuration $t'$ steps into the run from $b$. The halting hypothesis gives $G$ there. This proves the required invariant over the whole concatenated run.

**Key facts.** `Complexity.LogProg.mrun_add`.
