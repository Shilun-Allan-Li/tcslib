<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_host_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Ledger Bound

**Claim.** Under the stated bound on $T$, the total ledger expression is at most $(B+A+5)(n+C(n+1)^c+1)^{c+d+1}$.

**Proof.** Set $m=n+C(n+1)^c+1$, which is positive. Since $m\ge n+1$ and $m\\ge1$, monotonicity of powers gives $T\le B(n+1)^{c+1}\le Bm^{c+d+1}$. It also gives $A m^d\le A m^{c+d+1}$. For the remaining terms, first bound $3n+C(n+1)^c+5\le5m$ by expanding the definition of $m$; then use $m\le m^{c+d+1}$, since $c+d+1\ge1$. Thus those terms are at most $5m^{c+d+1}$. Adding the three bounds yields $(B+A+5)m^{c+d+1}$, and substituting the definition of $m$ proves the inequality.
