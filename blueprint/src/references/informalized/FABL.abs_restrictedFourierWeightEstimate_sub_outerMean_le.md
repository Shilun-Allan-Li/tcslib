<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_restrictedFourierWeightEstimate_sub_outerMean_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Weight Estimate to Outer Mean

**Claim.** The restricted Fourier weight estimate differs from the outer mean of the squared restricted coefficient by at most $3\varepsilon/4$.

**Proof.** The outer mean and the estimate are expectations over the same finite sample space, of the squared exact restricted coefficient and the squared estimated coefficient, respectively. By linearity, their difference is the expectation of the pointwise difference of these squares. The absolute value of an expectation is bounded by the expectation of the absolute value. For each sample, the exact coefficient has absolute value at most $1$, while the coefficient estimate is within $\varepsilon/4$ of it. Since $0<\varepsilon\le1/2$, the bound for the difference of squares gives an error at most $3\varepsilon/4$ at every sample. Averaging preserves this bound.

**Key facts.** `FABL.SmallBiasInput.epsilon_le_half`, `FABL.abs_restrictedFourierCoefficientEstimate_sub_le`, `FABL.abs_restrictionFourierCoeff_toReal_le_one`, `FABL.abs_sq_sub_sq_le_three_quarters`.
