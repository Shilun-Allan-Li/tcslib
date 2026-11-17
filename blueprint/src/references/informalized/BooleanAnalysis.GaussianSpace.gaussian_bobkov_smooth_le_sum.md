<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.gaussian_bobkov_smooth_le_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separated smooth Gaussian Bobkov bound

**Claim.** Under the stated hypotheses, the Gaussian profile of the mean of $f$ is at most the sum of the mean profile and the mean Euclidean norm of its coordinate derivatives.

**Proof.** The smooth Gaussian Bobkov inequality bounds the profile of the mean by the integral of the square root of the sum of the squared profile and squared coordinate derivatives. Both summands are integrable: the profile composed with $f$ is integrable by its range and finite-measure bound, and the gradient term is integrable because the derivative field is continuous and bounded. Pointwise, for nonnegative $a=U(f(x))$ and $b=\sqrt{\sum_i(D(x)e_i)^2}$, one has $\sqrt{a^2+b^2}\le a+b$, since both sides are nonnegative and $(a+b)^2\ge a^2+b^2$. Integrating this inequality and using linearity of the integral gives the claimed separated bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussian_bobkov_smooth`, `BooleanAnalysis.GaussianSpace.integrable_closedGaussianProfile_comp`, `BooleanAnalysis.GaussianSpace.integrable_gaussianGradient_of_bounded`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`.
