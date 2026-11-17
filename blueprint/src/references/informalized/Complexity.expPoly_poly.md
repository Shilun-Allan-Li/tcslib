<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.expPoly_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound for polynomials

**Claim.** For all natural numbers $a,d$, the function $n\mapsto a(n+1)^d$ is exponential-polynomial.

**Proof.** Choose $K=a+d$ and $k=1$. The inequality $a<2^a$ bounds the coefficient, while $n+1\le2^{n+1}$ bounds the base. Raising the latter inequality to the power $d$ gives $(n+1)^d\le2^{d(n+1)}$. Therefore $a(n+1)^d\le2^a2^{d(n+1)}=2^{a+d(n+1)}$. Since $n+1\ge1$, we have $a+d(n+1)\le(a+d)(n+1)$, which is the desired exponent $K(n+1)^k$.
