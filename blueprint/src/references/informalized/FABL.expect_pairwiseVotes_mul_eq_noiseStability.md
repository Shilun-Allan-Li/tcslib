<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.expect_pairwiseVotes_mul_eq_noiseStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairwise vote noise stability

**Claim.** For distinct pairwise contests, the average over ranking profiles of the product of a Boolean function's real-valued outputs on the two vote vectors equals its noise stability at correlation $-1/3$.

**Proof.** Apply the pairwise-vote Fourier sum formula with both cube functions equal to the real-valued version of the Boolean function (`expect_pairwiseVotes_mul_eq_fourier_sum`). The resulting sum has terms $(-1/3)^{|S|}\widehat f(S)^2$. The Fourier expansion of noise stability expresses noise stability at correlation $\rho$ as $\sum_S\rho^{|S|}\widehat f(S)^2$ (`noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`); take $\rho=-1/3$, which lies in $[-1,1]$ (`neg_one_third_mem_Icc`). The two sums agree term by term.

**Key facts.** `FABL.expect_pairwiseVotes_mul_eq_fourier_sum`, `FABL.neg_one_third_mem_Icc`, `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`.
