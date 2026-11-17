<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Call.lean :: Complexity.LogProg.runFrom_forall_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Run Intervals

**Claim.** If $Q$ holds along the first $T_1$ steps from $c$ and along the next $T_2$ steps from the configuration at time $T_1$, then it holds at every time up to $T_1+T_2$ from $c$.

**Proof.** Fix $t\le T_1+T_2$. If $t<T_1$, the first hypothesis gives $Q$ at time $t$. Otherwise write $t=T_1+t'$ with $t'=t-T_1$. The run-composition law identifies the configuration at time $t$ from $c$ with the configuration at time $t'$ from the configuration at time $T_1$ (`runFrom_add`). The bound on $t$ gives $t'\le T_2$, so the second hypothesis yields $Q$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
