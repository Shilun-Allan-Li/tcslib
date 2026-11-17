<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/ExpPoly.lean :: Complexity.ExpPoly.add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under sums

**Claim.** The sum of two exponential-polynomial functions is exponential-polynomial.

**Proof.** Choose bounds $T_i(n)\le 2^{K_i(n+1)^{k_i}}$ for $i=1,2$. Set $P=(n+1)^{\max(k_1,k_2)}$. Monotonicity of powers in the degree (`pow_mono_deg`) gives $(n+1)^{k_i}\le P$, so each summand is at most $2^{K_iP}$. Since $P\ge1$, both of these powers are at most $2^{(K_1+K_2)P}$. Their sum is therefore at most twice this common bound, which equals $2^{(K_1+K_2)P+1}$. Finally, $(K_1+K_2)P+1\le (K_1+K_2+1)P$, again because $P\ge1$. Thus the sum has the required form with constants $K_1+K_2+1$ and $\max(k_1,k_2)$.

**Key facts.** `Complexity.pow_mono_deg`.
