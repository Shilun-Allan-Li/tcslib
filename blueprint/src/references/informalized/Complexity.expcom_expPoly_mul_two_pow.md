<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_expPoly_mul_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound with a constant factor

**Claim.** For all natural numbers $A,K,k$, the function $n\mapsto A\,2^{K(n+1)^k}$ is exponential-polynomial.

**Proof.** Choose $K'=A+K$ and $k'=k$. Since $A<2^A$ and $1\le(n+1)^k$, we have $A\le2^A\le2^{A(n+1)^k}$. Multiplying by $2^{K(n+1)^k}$ gives a bound by $2^{A(n+1)^k}2^{K(n+1)^k}=2^{(A+K)(n+1)^k}$, which has the required form.
