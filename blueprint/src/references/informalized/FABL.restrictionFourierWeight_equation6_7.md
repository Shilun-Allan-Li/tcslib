<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictionWeights.lean :: FABL.restrictionFourierWeight_equation6_7 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased expectation and restricted Fourier weight

**Claim.** Under the stated bias, nonnegativity, normalization, and Fourier one-norm assumptions, the squared restricted coefficient has the claimed expectation deviation bound, and the resulting error factor is at most $\varepsilon/4$.

**Proof.** Put $F(z)=\widehat{f_{J\mid z}}(S)$ in the finite sign-cube coordinates. Since $s\ge1$, we have $s>0$ and $4s^2\ge0$, so $\varepsilon/(4s^2)\ge0$. Apply the biased-density estimate for squared sign functions (ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le) to $F$ with this bias parameter; it gives the first inequality directly. For the second, restriction cannot increase the Fourier one-norm (fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_le), so $\|\widehat F\|_1\le s$. Both norms are nonnegative, hence squaring preserves this bound and gives $\|\widehat F\|_1^2\le s^2$. Multiplying by the nonnegative bias parameter yields $\|\widehat F\|_1^2\,\varepsilon/(4s^2)\le s^2\,\varepsilon/(4s^2)=\varepsilon/4$, where the last equality uses $s>0$.

**Key facts.** `FABL.ProbabilityDensity.abs_expectation_signFunction_sq_sub_mean_sq_le`, `FABL.fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_le`, `FABL.fourierOneNorm_nonneg`.
