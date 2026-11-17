<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.fourierDegree_mul_coordinateSum_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree after multiplying by a coordinate sum factor

**Claim.** If $q$ has Fourier degree at most $d$, then $x\mapsto q(x)(\sum_i x_i-r)$ has Fourier degree at most $d+1$ for every real $r$.

**Proof.** By the degree criterion (`fourierDegree_le_iff`), fix a set $S$ with $|S|>d+1$. For each coordinate $i$, the symmetric difference $S\mathbin{\triangle}\{i\}$ has size at least $|S|-1>d$, since toggling one coordinate changes cardinality by at most one (`card_le_card_symmDiff_singleton_add_one`). Multiplying $q$ by the coordinate sign at $i$ shifts its Fourier coefficient at $S$ to the coefficient of $q$ at this symmetric difference (`fourierCoeff_mul_signValue`), which vanishes by the degree bound for $q$. Thus every term from the coordinate sum contributes zero to the coefficient at $S$. The constant part contributes a scalar multiple of the coefficient of $q$ at $S$, which also vanishes since $|S|>d$. Consequently the full coefficient at $S$ is zero, proving the stated degree bound.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.card_le_card_symmDiff_singleton_add_one`, `FABL.fourierCoeff_mul_signValue`.
