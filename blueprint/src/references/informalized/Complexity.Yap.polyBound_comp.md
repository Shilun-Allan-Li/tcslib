<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.polyBound_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound Under Composition

**Claim.** If $f$ is polynomially bounded, then $n\mapsto C(f(n)+1)^c$ is polynomially bounded for all natural numbers $C,c$.

**Proof.** Take a bound $f(n)\le A(n+1)^\alpha$. Because $(n+1)^\alpha\ge1$, we have $f(n)+1\le(A+1)(n+1)^\alpha$. Raising this inequality to the power $c$ and multiplying by $C$ gives $C(f(n)+1)^c\le C((A+1)(n+1)^\alpha)^c$. Distributing the power shows this equals $C(A+1)^c(n+1)^{\alpha c}$. Thus coefficient $C(A+1)^c$ and exponent $\alpha c$ provide the desired polynomial bound.
