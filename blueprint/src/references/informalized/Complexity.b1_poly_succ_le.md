<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.b1_poly_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial growth estimate

**Claim.** For all natural numbers $c,k,n$, $c(n^k+1)+1\le (2c+1)(n+1)^k$.

**Proof.** Since $n+1\ge 1$, we have $1\le (n+1)^k$. Also, $n\le n+1$ implies $n^k\le(n+1)^k$. Adding these inequalities gives $n^k+1\le 2(n+1)^k$. Multiplying by $c$ preserves the inequality, so $c(n^k+1)\le 2c(n+1)^k$. Adding $1\le(n+1)^k$ yields the desired bound, since $2c(n+1)^k+(n+1)^k=(2c+1)(n+1)^k$.
