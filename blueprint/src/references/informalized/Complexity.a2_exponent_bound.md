<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_exponent_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorbing a polynomial exponent

**Claim.** For all natural numbers $K,k$, there are natural numbers $A,e$ such that for every $n$, $2^{K(n+1)^k}\le A\cdot 2^{n^e}$.

**Proof.** Take $A=2^{K\cdot 2^k}$ and $e=K+2k$. If $n\ge2$, then $K\le n^K$ and $n+1\le n^2$. Raising the latter inequality to the $k$th power and multiplying by the former gives $K(n+1)^k\le n^{K+2k}=n^e$. Since powers of $2$ preserve order, $2^{K(n+1)^k}\le2^{n^e}\le A\cdot2^{n^e}$. If $n<2$, then $n+1\le2$, so $(n+1)^k\le2^k$ and $2^{K(n+1)^k}\le2^{K2^k}=A\le A\cdot2^{n^e}$.
