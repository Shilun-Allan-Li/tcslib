<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.Rch.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Bounded Reachability

**Claim.** Two finite runs with work-tape head positions between $-1$ and $W$ before their endpoints concatenate to a run with the same bounds before its endpoint.

**Proof.** Let the two run lengths be $T_1$ and $T_2$. The iterated-step addition identity (`Complexity.LogProg.rrun_add`) shows that a run of length $T_1+T_2$ from $a$ reaches $b$ after $T_1$ steps and then follows the second run to $c$. For a time $t<T_1+T_2$, if $t<T_1$, the first run gives both head-position bounds. Otherwise write $t=T_1+t'$. Then $t'<T_2$, and the addition identity identifies the configuration at time $t$ with the second run's configuration at time $t'$, which gives the same bounds.

**Key facts.** `Complexity.LogProg.rrun_add`.
