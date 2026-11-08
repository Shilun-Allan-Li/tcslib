<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AReach.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Constrained Reachability

**Claim.** Two finite runs whose configurations satisfy $G$ before their respective endpoints can be concatenated to give a run from $a$ to $c$ whose configurations satisfy $G$ before its endpoint.

**Proof.** Choose run lengths $T_1,T_2$ witnessing the two reachability claims. The iterated-step addition identity (`Complexity.LogProg.arun_add`) shows that running for $T_1+T_2$ steps from $a$ first reaches $b$ and then follows the second run to $c$. For any time $t<T_1+T_2$, if $t<T_1$, the first run's bound gives $G$ at time $t$. Otherwise write $t=T_1+t'$; then $t'<T_2$, and the addition identity identifies the configuration at time $t$ with the second run's configuration at time $t'$, where its bound gives $G$.

**Key facts.** `Complexity.LogProg.arun_add`.
