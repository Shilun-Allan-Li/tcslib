<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/P.lean :: Complexity.succ_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor power bound

**Claim.** For all natural numbers $n,d$, $(n+1)^d\le 2^d(n^d+1)$.

**Proof.** If $n=0$, the two sides reduce to $1$ and $2^d$, respectively, so the inequality holds. If $n>0$, then $n+1\le 2n$, hence $(n+1)^d\le(2n)^d=2^dn^d$. Since $n^d\le n^d+1$ and multiplication by $2^d$ preserves order, this is at most $2^d(n^d+1)$.
