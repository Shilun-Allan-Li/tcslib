<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/DegreeOne.lean :: BooleanAnalysis.ThresholdFunctions.biased_degreeOne_weight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Degree-One Weight Bound

**Claim.** For a Boolean-valued sign function whose mean has absolute value at least $1-\delta$, the degree-one Fourier weight is at most $4\delta^2\log(2/\delta)$, assuming $0\le1-\delta$.

**Proof.** Let $\sigma$ be the sign of the mean and define $g=(1-\sigma f)/2$. Since both $f$ and $\sigma$ take values in $\{1,-1\}$, $g$ takes only the values zero and one. Its mean is $(1-|\mathbb E f|)/2$, hence at most $\delta/2$. Each singleton Fourier coefficient of $g$ is $-\sigma/2$ times the corresponding coefficient of $f$: the constant contribution vanishes because a singleton Walsh character has mean zero, as follows from character orthogonality (`fourier_coeff_chi`) and the singleton character formula (`chiS_singleton`). Consequently the level-one weights satisfy $W_1[f]=4W_1[g]`, using the sum-of-squares expression for degree-one weight (`weightLevel_one_eq_sum_singleton`).

If $\delta=0$, then $g$ is nonnegative with mean zero, so it vanishes identically (`eq_zero_of_expect_eq_zero`), and the desired bound follows. If $W_1[g]=0$, the same bound is immediate. Otherwise, put $\gamma=\delta/2$, $c=\log(1/\gamma)=\log(2/\delta)$, and $t=\sqrt{2c}$. The hypotheses give $\gamma>0$ and $c\ge1/2$.

Choose a unit vector of coefficients $a$ whose linear form $L(x)=\sum_i a_i\,\mathrm{sign}(x_i)$ correlates with $g$ by exactly $r=\sqrt{W_1[g]}$; this is provided by `exists_unit_linear_form`. Pointwise, when $g=0$ the following inequality is immediate, and when $g=1$ it follows from $1+u\le e^u$:
\[
tgL\le (t^2/2+c-1)g+\gamma e^{-t^2/2}e^{tL}.
\]
Taking expectations, using monotonicity and linearity of expectation (`expect_mono`, `expect_add`, `expect_const_mul`), the bound $\mathbb E g\le\gamma$, and the Rademacher moment-generating-function estimate for a unit coefficient vector (`rademacher_mgf_le`), gives $tr\le2\gamma c$. Since $t>0$ and $t^2=2c$, this implies $r\le\gamma t$. Finally, $W_1[f]=4r^2$, so $W_1[f]\le4\gamma^2t^2=2\delta^2c\le4\delta^2\log(2/\delta)$, as required.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.thresholdSign_pm_one`, `BooleanAnalysis.ThresholdFunctions.mul_thresholdSign_self`, `BooleanAnalysis.ThresholdFunctions.expect_add`, `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.ThresholdFunctions.fourier_coeff_chi`, `BooleanAnalysis.chiS_singleton`, `BooleanAnalysis.ThresholdFunctions.weightLevel_one_eq_sum_singleton`, `BooleanAnalysis.ThresholdFunctions.eq_zero_of_expect_eq_zero`, `BooleanAnalysis.ThresholdFunctions.weightLevel_nonneg`, `BooleanAnalysis.ThresholdFunctions.exists_unit_linear_form`, `BooleanAnalysis.ThresholdFunctions.rademacher_mgf_le`, `BooleanAnalysis.ThresholdFunctions.expect_mono`.
