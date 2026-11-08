<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Poly_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bounds Under Powers

**Claim.** If $f$ is polynomially bounded and $a,d\in\mathbb N$, then $n\mapsto a(f(n)+1)^d$ is polynomially bounded.

**Proof.** Choose $b,e$ so that $f(n)\le b(n+1)^e$ for every $n$. Since $(n+1)^e\ge1$, adding this inequality gives $f(n)+1\le(b+1)(n+1)^e$. Raising both sides to the $d$th power and multiplying by $a$ bounds the target by $a(b+1)^d(n+1)^{ed}$. This has the required polynomial-bound form.
