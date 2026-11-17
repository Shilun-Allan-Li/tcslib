<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.searchDown_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Descending Search Reaches the First Positive Test

**Claim.** If $c$ satisfies $P$ and $c_0>c$ is a larger value with no intermediate value satisfying $P$, repeated decrements from $c_0$ reach the test at $c$, which then enters $\mathrm{yes}$. Every configuration before the final one satisfies the precondition and the register bound.

**Proof.** Fix $c_0$ and induct on $k=c_0-(c+1)$. At the base, $c_0=c+1$. From the starting $\mathrm{dec}$ configuration, the decrement instruction lowers register $r$ to $c$ and returns to $\mathrm{test}$. The test hypothesis and $P(c)$ then take the machine to $\mathrm{yes}$ without changing the valuation. Both intermediate configurations satisfy the guard: the test state has the assumed precondition, the decrement state satisfies it by the definition of the precondition and the instruction at $\mathrm{dec}$, and the register bound follows because the updated value is at most $B$. For the induction step, the maximality assumption implies $\neg P(c_0-1)$, since $c<c_0-1<c_0$. The decrement therefore reaches a test at $c_0-1$, where the test hypothesis sends the machine back to $\mathrm{dec}$ with that value unchanged. Apply the induction hypothesis from this new decrement configuration: the distance from $c$ has decreased by one, and the no-intermediate-positive condition is inherited. The two new pre-final configurations satisfy the guard by the same precondition and register-bound arguments. Prepending these two steps to the inductive run proves the reachability claim.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.refl`.
