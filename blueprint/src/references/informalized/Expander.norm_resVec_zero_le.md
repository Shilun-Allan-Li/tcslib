<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.norm_resVec_zero_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial restricted-vector norm bound

**Claim.** For positive $n$, if $B$ has size at most $\beta n$ with $\beta\ge 0$, then the initial vector, equal to $1/n$ on $B$ and zero elsewhere, has norm at most $\sqrt{\beta}/\sqrt{n}$.

**Proof.** Since $n>0$, its reciprocal is defined. The squared Euclidean norm is the sum of the squared coordinates, so it equals $|B|(1/n)^2$. The hypothesis $|B|\le \beta n$ bounds this by $\beta n(1/n)^2=\beta/n$. Finally, $\sqrt{\beta}/\sqrt{n}=\sqrt{\beta/n}$, and taking square roots preserves the inequality.
