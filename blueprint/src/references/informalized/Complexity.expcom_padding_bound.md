<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_padding_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Padding Bound

**Claim.** For all natural numbers a, b, c, and n, the stated quadratic expression is bounded by the specified power of two.

**Proof.** Write $E=2^{n^c}$. Since $E\geq 1$, we have $aE+1\leq(a+1)E$. Also $a+1<2^{a+1}$, so $aE+1\leq 2^{a+1}E=2^{a+1+n^c}$. The factor $b$ is at most $2^b$. Therefore the left side is at most $2^{b+2(a+1+n^c)}$. Finally, $1\leq(n+1)^c$ and $n^c\leq(n+1)^c$, so the exponent $b+2(a+1+n^c)$ is at most $(b+2(a+1)+2)(n+1)^c$. Monotonicity of powers of two gives the asserted bound.
