<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Controller.lean :: FABL.heavy_prefix_mem_goldreichLevinRetained_of_stageAccurate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Heavy Prefix Retention from Stage Accuracy

**Claim.** If a Fourier coefficient has magnitude at least $\tau$ and the weight estimates are accurate for all candidates at a given stage, then the next prefix of its frequency belongs to that stage's retained set.

**Proof.** Let $J$ be the first $k+1$ coordinates and let $S$ be the $(k+1)$-coordinate prefix of $U$. Because the preceding prefix is active, $S$ is among the candidates generated at coordinate $k$ (`prefixFrequency_succ_mem_goldreichLevinCandidates`). Its free-coordinate part in $J$ agrees with that of $U$ (`freeFrequencyPart_prefixFrequency`), and the squared coefficient at $U$ is bounded by the restricted Fourier weight of this bucket (`sq_fourierCoeff_le_restrictedFourierWeight`). The heavy-coefficient hypothesis makes this weight at least $\tau^2$. Stage accuracy says the estimate is less than $\tau^2/4$ below the true weight, so the estimate is greater than $3\tau^2/4$, in particular greater than the retention threshold $\tau^2/2$. Hence $S$ passes the retention filter.

**Key facts.** `FABL.prefixFrequency_succ_mem_goldreichLevinCandidates`, `FABL.freeFrequencyPart_prefixFrequency`, `FABL.sq_fourierCoeff_le_restrictedFourierWeight`.
