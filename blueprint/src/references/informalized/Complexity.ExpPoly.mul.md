<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.ExpPoly.mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Products

**Claim.** If $T_1$ and $T_2$ are exponential-polynomial, then $n\mapsto T_1(n)T_2(n)$ is exponential-polynomial.

**Proof.** Choose witnesses $K_1,k_1$ and $K_2,k_2$ for the exponential-polynomial bounds on $T_1$ and $T_2$. Set $k=\max(k_1,k_2)$ and, for each $n$, let $P=(n+1)^k$. Since $n+1\ge1$, increasing the exponent does not decrease its power, so $(n+1)^{k_1}\le P$ and $(n+1)^{k_2}\le P$. The two assumed bounds therefore give
\[
T_1(n)T_2(n)\le 2^{K_1P}2^{K_2P}=2^{(K_1+K_2)P}.
\]
Hence $K_1+K_2$ and $k$ witness that the product is exponential-polynomial.

**Key facts.** `Complexity.pow_mono_deg`.
