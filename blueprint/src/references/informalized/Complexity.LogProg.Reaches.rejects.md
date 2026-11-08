<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.Reaches.rejects -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reaching followed by rejection

**Claim.** If $c_0$ reaches $c_1$ relative to $c,r,p$, and the computation from $c_1$ rejects relative to $c,r,p$, then the computation from $c_0$ rejects relative to $c,r,p$.

**Proof.** Let $T_1$ be a time witnessing that $c_0$ reaches $c_1$, and let $T_2$ witness rejection from $c_1$. Run from $c_0$ for $T_1+T_2$ steps: the run-composition identity (\texttt{rrun_add}) and the endpoint equality at time $T_1$ identify this with running from $c_1$ for $T_2$ steps. Thus it has the same halting state, rejecting output, and register-head positions required by the rejection witness. For any intermediate time $t<T_1+T_2$, split into two cases. If $t<T_1$, the reaching witness supplies the required reference form and absence of an oracle call. Otherwise write $t=T_1+t'$; composing the runs shows that the configuration at $t$ is the one at time $t'$ from $c_1$, and $t'<T_2$, so the rejection witness supplies the required condition.

**Key facts.** `Complexity.LogProg.rrun_add`.
