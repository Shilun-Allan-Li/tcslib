<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_bridge_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bridge Bound

**Claim.** If $\mathrm{len}\le A(n+1)^d$, then $c\bigl(A(n+1)^d+n+\mathrm{len}+1\bigr)+1\le (c(2A+1)+1)(n+1)^{d+1}$.

**Proof.** Put $P=(n+1)^{d+1}$. Since $n+1\ge1$, increasing the exponent from $d$ to $d+1$ shows $A(n+1)^d\le AP$, and the hypothesis gives $\mathrm{len}\le AP$. Also $n\le P$ and $1\le P$. Thus $A(n+1)^d+n+\mathrm{len}+1\le(2A+1)P$. Multiplying by $c$ and using $1\le P$ yields $c( A(n+1)^d+n+\mathrm{len}+1)+1\le c(2A+1)P+P=(c(2A+1)+1)(n+1)^{d+1}$.
