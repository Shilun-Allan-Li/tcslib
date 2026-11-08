<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepTime_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic simulation time bound

**Claim.** For all natural numbers $k,t$, the recursively defined time function satisfies $\sigma_k(t)\leq (9k+6)(t+1)^2$.

**Proof.** Use the closed form for the simulation time (`sweepTime_eq`). Each of $t^2$, $t$, and $1$ is at most $(t+1)^2$: the first follows from $t\leq t+1$, the second from $t\leq (t+1)^2$, and the last from $1\leq (t+1)^2$. Multiplying these inequalities by their nonnegative coefficients bounds the closed form by $[2k+(5k+4)+(2k+2)](t+1)^2$. The coefficient simplifies to $9k+6$, giving the claim.

**Key facts.** `Turing.FinTM.sweepTime_eq`.
