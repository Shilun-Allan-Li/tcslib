<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.succ_pow_le_quasiPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial power quasi-polynomial bound

**Claim.** For all natural numbers $n,c$, $(n+1)^c\le 2^{c(c+1)}2^{(\log_2 n)^2}$, with $\log_2 n$ the integer logarithm to base $2$.

**Proof.** Set $m=\log_2 n$. The defining bound for the integer logarithm gives $n+1\le 2^{m+1}$. Also, $(m+1)c\le c(c+1)+m^2$: if $m\le c$, this follows by bounding $(m+1)c$ by $(c+1)c$; if $m>c$, the difference $m^2-(m+1)c+c(c+1)$ is nonnegative. Raising the first inequality to the power $c$, then using monotonicity of powers of $2$ and the exponent inequality, yields $(n+1)^c\le2^{c(c+1)+m^2}$. Splitting this exponent as a sum gives the stated product.
