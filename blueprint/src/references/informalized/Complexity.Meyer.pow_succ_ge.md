<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Meyer.lean :: Complexity.Meyer.pow_succ_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Power Bound for Natural Numbers

**Claim.** For all natural numbers $n,c$, one has $n^c+n\le (n+1)^{c+1}$.

**Proof.** Since $n\le n+1$, monotonicity of natural-number powers gives $n^c\le(n+1)^c$. Also $(n+1)^c\ge1$, because $n+1
e0$. By the successor power identity, the right side is $(n+1)^c(n+1)=(n+1)^c n+(n+1)^c$. The first term is at least $n$, and the second is at least $n^c$; together they are at least $n+n^c$.
