<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.whileDone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Immediate loop termination

**Claim.** If the guard is safe and false initially, $Q$ holds initially, and the guard-check cost is at most $T$, then the loop ends within time $T$ in a state satisfying $Q$.

**Proof.** Use the false-guard loop execution rule: the loop leaves the state unchanged and costs $c.cost+1$. Thus the final state is $\sigma$ (the initial state), where $Q$ holds, and the assumed inequality bounds the execution cost by $T$.
