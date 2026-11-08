<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_bridge_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bridge Bound

**Claim.** If $\ell\le A(n+1)^d$, then $c\bigl(A(n+1)^d+n+\ell+1\bigr)+1\le\bigl(c(2A+1)+1\bigr)(n+1)^{d+1}$.

**Proof.** Put $X=(n+1)^{d+1}$. Since $n+1\ge1$, increasing the exponent from $d$ to $d+1$ gives $A(n+1)^d\le AX$, and $n\le X$. The hypothesis also gives $\ell\le A(n+1)^d\le AX$. Thus the sum inside the parentheses is at most $(2A+1)X$. Multiplying by $c$ and using $1\le X$ yields $c(2A+1)X+1\le(c(2A+1)+1)X$, as required.
