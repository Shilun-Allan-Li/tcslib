<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.whileStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One bounded loop iteration

**Claim.** If the guard is safe and true, the body can execute within time $T_1$ to a state from which the loop ends within time $T_2$ satisfying $Q$, and the combined cost bound is at most $T$, then the loop ends within time $T$ satisfying $Q$.

**Proof.** Unpack the two bounded-execution witnesses: the body runs from $\sigma$ to an intermediate state at cost at most $T_1$, and the loop then runs from that state to a final state at cost at most $T_2$ satisfying $Q$. Since the guard is safe and true initially, the true-guard execution rule combines these runs into one loop execution, adding the guard-check cost $c.cost+1$. The assumed inequality bounds this combined cost by $T$, and the final state still satisfies $Q$.
