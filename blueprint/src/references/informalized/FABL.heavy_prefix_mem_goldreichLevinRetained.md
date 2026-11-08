<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.heavy_prefix_mem_goldreichLevinRetained -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Heavy Prefix Retention

**Claim.** If a Fourier coefficient has magnitude at least $\tau$, then, assuming the restricted Fourier-weight estimates have error less than $\tau^2/4$, the next prefix of its frequency belongs to the retained set.

**Proof.** Let $J$ be the first $k+1$ coordinates and let $S$ be the $(k+1)$-coordinate prefix of $U$. The preceding $k$-coordinate prefix is active, so the next prefix is among the candidates generated at coordinate $k$ (`prefixFrequency_succ_mem_goldreichLevinCandidates`). The free-coordinate part of $S$ in $J$ agrees with that of $U$ (`freeFrequencyPart_prefixFrequency`). The squared coefficient at $U$ is therefore bounded by the restricted Fourier weight of this bucket (`sq_fourierCoeff_le_restrictedFourierWeight`). Since $|\widehat f(U)|\ge\tau$, that weight is at least $\tau^2$. The estimate differs from the true bucket weight by less than $\tau^2/4$, so it is strictly greater than $3\tau^2/4$, and hence greater than the retention threshold $\tau^2/2$. Thus $S$ is a candidate whose estimated weight exceeds the threshold, exactly the condition for membership in the retained set.

**Key facts.** `FABL.prefixFrequency_succ_mem_goldreichLevinCandidates`, `FABL.freeFrequencyPart_prefixFrequency`, `FABL.sq_fourierCoeff_le_restrictedFourierWeight`.
