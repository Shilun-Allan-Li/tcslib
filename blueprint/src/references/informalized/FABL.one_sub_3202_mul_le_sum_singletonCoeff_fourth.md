<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.one_sub_3202_mul_le_sum_singletonCoeff_fourth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Powers of Singleton Fourier Coefficients

**Claim.** If $0\le\delta\le1/1600$ and the total Fourier weight at level $1$ is $1-\delta$, then $1-3202\delta\le\sum_{i=1}^n\widehat f(\{i\})^4$.

**Proof.** Write $a_i=\widehat f(\{i\})$ and let $s=\sum_i a_i^2$. Level-one Fourier weight equals the sum of the squared singleton coefficients (`FABL.fourierWeightAtLevel_one_eq_sum_singleton`), so $s=1-\delta$. The centered-square estimate (`FABL.expect_centeredSingletonSquare_sq_le`) bounds the expectation of the squared centered linear form by $6400\delta$. On the other hand, its exact second-moment identity (`FABL.expect_centeredLinearSquare_sq`) says that half this expectation is $s^2-\sum_i a_i^4$. Therefore $\sum_i a_i^4\ge (1-\delta)^2-3200\delta=1-3202\delta+\delta^2$. Since $\delta^2\ge0$, the desired bound follows.

**Key facts.** `FABL.expect_centeredSingletonSquare_sq_le`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.expect_centeredLinearSquare_sq`.
