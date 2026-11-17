<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_guess_time_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial envelope bound

**Claim.** For all natural numbers $C,c,K,r,n$, the polynomial expression on the left is bounded by the stated envelope involving $C+1$, $2^{r\max(1,c)}$, and $n^{r\max(1,c)}+1$.

**Proof.** Set $d=\max(1,c)$. Since $n+1>0$ and $1,c\le d$, monotonicity of natural powers gives $n+1\le(n+1)^d$ and $(n+1)^c\le(n+1)^d$. Consequently, $n+C(n+1)^c+1\le(C+1)(n+1)^d$: the terms $n+1$ are bounded by $(n+1)^d$, and the remaining term by $C(n+1)^d$. Raising this inequality to the power $r$ and multiplying by $K$ preserves the bound. The power laws rewrite the resulting expression as $K(C+1)^r(n+1)^{rd}$. Finally, the successor-power estimate $(n+1)^e\le 2^e(n^e+1)$, applied with $e=rd$ (the lemma `Complexity.succ_pow_le`), gives the desired inequality after rearranging factors.

**Key facts.** `Complexity.succ_pow_le`.
