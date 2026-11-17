<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Meyer.lean :: Complexity.Meyer.width_ok -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sufficient Width Bound

**Claim.** For $W=(c_0+3)(n+1)^{c+1}$, one has $n+2<2^W$ and $c_0(2^n)^c\le 2^W-1$.

**Proof.** The power-growth estimate $n^c+n\le(n+1)^{c+1}$ ( `Complexity.Meyer.pow_succ_ge`), together with $(n+1)^{c+1}\ge1$, gives $c_0+n^c+(n+2)\le W$. Monotonicity of powers of $2$ then bounds $2^{c_0+n^c+n+2}$ by $2^W$. Splitting the exponent shows that this lower bound is $2^{c_0}\,2^{n^c}\,2^{n+2}$, with $2^{n^c}=(2^n)^c$. For the first conclusion, $n+2<2^{n+2}$, and the other two factors are positive integers, so $n+2<2^{c_0}2^{n^c}2^{n+2}\le2^W$. For the second, use $c_0+1\le2^{c_0}$ and $1\le n+2$ to obtain $c_0(2^n)^c+1\le(c_0+1)(2^n)^c(n+2)\le2^{c_0}2^{n^c}2^{n+2}\le2^W$. Since all quantities are natural numbers, this implies $c_0(2^n)^c\le2^W-1$.

**Key facts.** `Complexity.Meyer.pow_succ_ge`.
