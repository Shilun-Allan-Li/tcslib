<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.mul_pow_le_mul_pow_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of a Power Bound

**Claim.** For natural numbers $C,n,d$, one has $C(n+1)^d\le C(n+1)^{d+1}$.

**Proof.** Since $n+1\ge 1$, raising it to the larger exponent gives $(n+1)^d\le(n+1)^{d+1}$. Multiplying this inequality by the nonnegative number $C$ preserves the order, yielding the claim.
