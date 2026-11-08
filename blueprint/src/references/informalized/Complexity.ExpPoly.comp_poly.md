<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.ExpPoly.comp_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition with a polynomial argument

**Claim.** If $T$ is exponential-polynomial, then $n\mapsto T(a(n+1)^d)$ is exponential-polynomial for every pair of natural numbers $a,d$.

**Proof.** Choose constants $K,k$ with $T(m)\le2^{K(m+1)^k}$ for every $m$. Because $(n+1)^d\ge1$, we have $a(n+1)^d+1\le(a+1)(n+1)^d$. Raising to the $k$th power and multiplying by $K$ preserves this bound, so
\[T(a(n+1)^d)\le 2^{K(a+1)^k(n+1)^{dk}}.\]
Here the exponent factors as $(a+1)^k(n+1)^{dk}$ by the laws of powers. The displayed bound has exponential-polynomial form, with constants $K(a+1)^k$ and $dk$.
