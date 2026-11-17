<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Separation.lean :: Complexity.eventually_poly_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial growth is eventually exponential-bounded

**Claim.** For any natural numbers $A$ and $K$, there is an $N$ such that for every $n\ge N$, $A(n+1)^K\le 2^n$.

**Proof.** Set $d=K+1$ and choose $N=d\,A d^K$. For $n\ge N$, write $m=\lfloor n/d\rfloor$. The threshold gives $A d^K\le m$, while division gives $dm\le n$ and $n+1\le d(m+1)$. Also $m+1\le 2^m$. Therefore
\[
A(n+1)^K\le A\bigl(d(m+1)\bigr)^K=(A d^K)(m+1)^K\le 2^m(2^m)^K=2^{(K+1)m}=2^{dm}\le 2^n.
\]
Here the last inequality uses monotonicity of powers of $2$ and $dm\le n$.
