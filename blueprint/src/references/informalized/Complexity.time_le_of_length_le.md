<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.time_le_of_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial bound from input length

**Claim.** For natural numbers $K,e,B,D,n,m$, if $m+1\le B(n+1)^D$, then $K(m+1)^e\le KB^e2^{De}(n^{De}+1)$.

**Proof.** Raise the assumed inequality to the power $e$ and multiply by $K$, which preserves the inequality for natural numbers. Rewrite the resulting power using $(ab)^e=a^eb^e$ and $(x^D)^e=x^{De}$, obtaining $KB^e(n+1)^{De}$. The estimate $(n+1)^d\le 2^d(n^d+1)$, applied with $d=De$ (the fact `succ_pow_le`), bounds this by $KB^e2^{De}(n^{De}+1)$.

**Key facts.** `Complexity.succ_pow_le`.
