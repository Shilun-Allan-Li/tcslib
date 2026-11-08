<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.Reaches.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of reaching

**Claim.** If $c_0$ reaches $c_1$ and $c_1$ reaches $c_2$, both relative to $c,r,p$, then $c_0$ reaches $c_2$ relative to $c,r,p$.

**Proof.** Let $T_1,T_2$ be witnessing times for the two reaching relations. The run-composition identity (\texttt{rrun_add}) shows that running from $c_0$ for $T_1+T_2$ steps is the same as continuing from $c_1$ for $T_2$ steps, so the endpoint is $c_2$. For an intermediate time $t<T_1+T_2$, if $t<T_1$, use the first reaching witness. Otherwise write $t=T_1+t'$; composition identifies the configuration at $t$ with the one at time $t'$ from $c_1$, where $t'<T_2$, so the second witness gives the required reference form and absence of an oracle call.

**Key facts.** `Complexity.LogProg.rrun_add`.
