<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.fourierWeightAtLevel_one_le_of_abs_mean_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Weight Near a Constant

**Claim.** If a Boolean sign function has mean whose absolute value is at least $1-\delta$, with $1-\delta\geq0$, then its level-one Fourier weight is at most $4\delta^2\log_2(2/\delta)$.

**Proof.** The proof replaces the function by its minority indicator, whose mean is $(1-|\mathbb E f|)/2$ and whose level-one weight is one quarter of the original weight. First, the absolute mean is at most one, so $0\leq\delta\leq1$. If $\delta=0$, the minority indicator has mean zero and hence level-one weight zero; the desired bound follows. Otherwise let $\alpha$ be the minority indicator's mean. It is nonnegative and at most $\delta/2\leq1/2$. If $\alpha=0$, its level-one weight again vanishes. For $\alpha>0$, the sharp level-one inequality gives weight at most $2\alpha^2\ln(1/\alpha)$ (`sharpLevelOneInequality`). The function $x^2\ln(1/x)$ is increasing for $0<x\leq1/2$ (`sq_mul_log_inv_mono`), so this is at most $2(\delta/2)^2\ln(2/\delta)$. Multiplying by four to return to the original function gives $2\delta^2\ln(2/\delta)$. Finally, since $2\leq4/\ln 2$, this is at most $4\delta^2\log_2(2/\delta)$, using the change-of-base identity. The zero-mean cases are handled separately so no logarithm at a zero argument is needed.

**Key facts.** `FABL.abs_mean_toReal_le_one`, `FABL.fourierWeightAtLevel_one_eq_four_mul_nearlyConstantMinorityIndicator`, `FABL.mean_nearlyConstantMinorityIndicator`, `FABL.sharpLevelOneInequality_eq_zero`, `FABL.mean_nearlyConstantMinorityIndicator_nonneg`, `FABL.mean_nearlyConstantMinorityIndicator_le`, `FABL.nearlyConstantMinorityIndicator_mem_Icc`, `FABL.sharpLevelOneInequality`, `FABL.sq_mul_log_inv_mono`.
