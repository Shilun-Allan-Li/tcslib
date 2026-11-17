<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.exists_one_div_sqrt_two_mul_dimension_le_influence_of_balanced_linearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of a Balanced Threshold

**Claim.** For a balanced linear threshold function on the sign cube of dimension $n\ge 1$, some coordinate has influence at least $1/\sqrt{2n}$.

**Proof.** A linear threshold function is unate, meaning that each coordinate has a fixed direction of monotonicity. First, the level-one Fourier weight is at least $1/2$: the threshold Fourier-weight bound gives weight at most one at least $1/2$ (`one_half_le_fourierWeightAtMost_one_of_isLinearThreshold`), and the weight decomposition into the empty set and singleton sets (`fourierWeightAtMost_one_eq_empty_add_sum_singleton`), together with balance forcing the empty-set coefficient to vanish (`isBalanced_iff_fourierCoeff_empty_eq_zero`), leaves at least $1/2$ in the singleton coefficients. Unateness identifies the absolute value of each singleton coefficient with the corresponding influence (`abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate`), so the sum of squared influences is at least $1/2$. If every influence were below $c=1/\sqrt{2n}$, nonnegativity of influences and $c>0$ would imply that each squared influence is below $c^2$. Since there are $n$ coordinates, their sum would be strictly below $nc^2=1/2$, a contradiction. Thus at least one coordinate has influence at least $1/\sqrt{2n}$.

**Key facts.** `FABL.one_half_le_fourierWeightAtMost_one_of_isLinearThreshold`, `FABL.fourierWeightAtMost_one_eq_empty_add_sum_singleton`, `FABL.isBalanced_iff_fourierCoeff_empty_eq_zero`, `FABL.isUnate_of_isLinearThreshold`, `FABL.abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate`, `FABL.influence_nonneg`.
