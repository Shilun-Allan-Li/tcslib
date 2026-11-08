<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.decideJuntaConstant_isCorrect_of_close -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Junta Constant Test

**Claim.** If a Boolean function depends on at most $k$ coordinates and a rational estimate is within $\eta_k=2^{-(k+2)}$ of its uniform mean, the stated threshold test correctly distinguishes the constant $1$, constant $-1$, and nonconstant cases.

**Proof.** Replace the empty-set Fourier coefficient in the closeness assumption by the uniform mean, using that the mean equals the empty-set Fourier coefficient (\texttt{mean_eq_fourierCoeff_empty}). Split into whether the target is constant. If it is constant, its value is either $1$ or $-1$. For the constant $1$, the mean is $1$ (using \texttt{signValue_one}); the error bound places the estimate strictly above $1-2\eta_k$, so the test declares $1$. For the constant $-1$, the mean is $-1$ (using \texttt{signValue_neg_one}); the error bound places the estimate strictly below $-(1-2\eta_k)$, so the test declares $-1$. In the remaining case, the junta mean bound says $|\operatorname{mean}(f)|\le 1-2^{-k}$ (\texttt{abs_mean_le_one_sub_inv_two_pow_of_isKJunta_of_nonconstant}). The identity $2^{-k}=4\eta_k$ (\texttt{inv_two_pow_eq_four_mul_juntaConstantAccuracy}) and the threshold and accuracy cast identities (\texttt{juntaConstantThreshold_cast}, \texttt{juntaConstantAccuracy_cast}) show, using the error bound, that the estimate lies between the two strict decision thresholds. Thus the test declares the function nonconstant.

**Key facts.** `FABL.mean_eq_fourierCoeff_empty`, `FABL.signValue_one`, `FABL.juntaConstantAccuracy_cast`, `FABL.juntaConstantThreshold_cast`, `FABL.signValue_neg_one`, `FABL.abs_mean_le_one_sub_inv_two_pow_of_isKJunta_of_nonconstant`, `FABL.inv_two_pow_eq_four_mul_juntaConstantAccuracy`.
