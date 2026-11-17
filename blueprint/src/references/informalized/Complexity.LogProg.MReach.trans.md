<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Reachability

**Claim.** If the machine reaches $b$ from $a$ while $G$ holds at every configuration before $b$, and reaches $c$ from $b$ while $G$ holds at every configuration before $c$, then it reaches $c$ from $a$ with $G$ holding at every configuration before $c$.

**Proof.** Let the two run lengths be $T_1$ and $T_2$. The combined run has length $T_1+T_2$: splitting an iterated run into its first $T_1$ steps and next $T_2$ steps gives this endpoint by the run-addition identity (`Complexity.LogProg.mrun_add`) and the two endpoint hypotheses. For any time $t<T_1+T_2$, if $t<T_1$, the first reachability hypothesis gives $G$ at time $t$. Otherwise write $t=T_1+t'$; then $t'<T_2$, and the run-addition identity identifies the configuration at time $t$ with the configuration at time $t'$ in the second run. The second reachability hypothesis therefore supplies $G$ there as well.

**Key facts.** `Complexity.LogProg.mrun_add`.
