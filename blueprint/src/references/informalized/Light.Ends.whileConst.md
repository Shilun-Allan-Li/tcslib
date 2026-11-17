<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.whileConst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-cost bounded loop

**Claim.** If the invariant holds initially, each of the first $n$ iterations safely takes the loop guard and executes the body within time $b$ while advancing the invariant, and the guard is safely false at the invariant’s $n$th stage with postcondition $Q$, then the loop ends within time $T$ under the stated bound.

**Proof.** Apply the general bounded-loop theorem (`Ends.while`) with the constant body-cost function that assigns cost $b$ to every iteration. Its iteration hypotheses and terminal hypothesis are precisely the assumptions given here. The theorem gives the loop within the sum of the per-round costs and final guard-check cost; with constant body cost this sum is $n(c.cost+1+b)+(c.cost+1)$. The assumed inequality bounds that quantity by $T$, and monotonicity of the time bound (`Ends.mono`) raises the bound to $T$ while leaving the postcondition unchanged.

**Key facts.** `Light.Ends.while`, `Light.Ends.mono`.
