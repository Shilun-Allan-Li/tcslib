<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.expPoly_exp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound for exponentials

**Claim.** For all natural numbers $c,e$, the function $n\mapsto c\,2^{n^e}$ is exponential-polynomial.

**Proof.** Choose $K=c+1$ and $k=e$. Since $c<2^c$, and $n\le n+1$, monotonicity of powers gives $n^e\le(n+1)^e$. Thus $c\,2^{n^e}\le 2^c2^{(n+1)^e}=2^{c+(n+1)^e}$. Also $1\le(n+1)^e$, including when $e=0$, so $c+(n+1)^e\le(c+1)(n+1)^e$. Monotonicity of powers of $2$ yields the required bound.
