<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumExponent_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Bound for Polynomial Exponents

**Claim.** For any natural numbers $K$ and $k$, there are natural numbers $A,e$ such that $2^{K(n+1)^k}\le A(2^n)^e$ for every natural number $n$.

**Proof.** Choose $A=2^{K2^k}$ and $e=K+2k$. If $n\ge2$, then $K\le n^K$ (since $K<2^K\le n^K$), and $n+1\le n^2$. Hence $K(n+1)^k\le n^K(n^2)^k=n^{K+2k}$. Raising $2$ to these exponents bounds the left side by $2^{n^{K+2k}}$. Since $n^{K+2k}\le 2^n{}^{K+2k}$, this is at most $(2^n)^{K+2k}$, and thus at most $A(2^n)^e$. If $n<2$, then $n+1\le2$, so $K(n+1)^k\le K2^k$; consequently the left side is at most $A$, which is at most $A(2^n)^e$.
