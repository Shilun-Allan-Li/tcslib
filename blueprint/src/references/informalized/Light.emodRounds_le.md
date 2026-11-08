<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Emod.lean :: Light.emodRounds_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on remainder rounds

**Claim.** If $a\le V$, then the binary size of $\lfloor a/M\rfloor$ is at most $\lfloor\log_2(V+1)\rfloor+1$.

**Proof.** By the definition of the number of rounds, it suffices to bound the binary size of $a/M$. For natural numbers, division does not increase the dividend, so $a/M\le a\le V<V+1$. The defining upper-bound property of the base-two logarithm gives $V+1<2^{\lfloor\log_2(V+1)\rfloor+1}$. Hence $a/M$ is strictly below this power of two, which is precisely the bound on its binary size.
