<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoop_polyBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Closure Under Products

**Claim.** If $P$ and $R$ are polynomially bounded, then $n\mapsto c(P(n)+1)(R(n)+2)$ is polynomially bounded for every natural number $c$.

**Proof.** Choose bounds $P(n)\le a(n+1)^d$ and $R(n)\le b(n+1)^e$. Since $(n+1)^d$ and $(n+1)^e$ are at least one, these imply $P(n)+1\le(a+1)(n+1)^d$ and $R(n)+2\le(b+2)(n+1)^e$. Multiplying the inequalities by the nonnegative factors gives
\[c(P(n)+1)(R(n)+2)\le c(a+1)(b+2)(n+1)^{d+e}.\]
Here the exponents combine by the law of exponents. Thus the product has polynomial bound with coefficient $c(a+1)(b+2)$ and degree $d+e$.
