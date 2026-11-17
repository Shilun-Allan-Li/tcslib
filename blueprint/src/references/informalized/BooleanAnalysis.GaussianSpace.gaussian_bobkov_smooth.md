<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.gaussian_bobkov_smooth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Smooth Gaussian Bobkov inequality

**Claim.** Under the stated range, differentiability, Lipschitz, and boundedness hypotheses, the Gaussian profile of the mean of $f$ is at most the Gaussian mean of the square root of the squared profile plus the sum of squared coordinate derivatives.

**Proof.** First, differentiability of $f$ at every point implies that $f$ is continuous. Regard it as a bounded continuous function $F$; the range condition ensures the required bound. The bounded-continuous-integrand construction supplies a bounded continuous function $G$ whose value is the stated square root. Along normalized sums of independent signs, apply the discrete Bobkov inequality to $f$. Its right side is the expectation of $G$ plus a gradient error. The expectations of $F$ and $G$ along these normalized sums converge to their Gaussian integrals, while the gradient error tends to zero. Continuity of the closed Gaussian profile carries convergence of the means through that profile. Passing to the limit in the discrete inequalities gives the asserted Gaussian inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.exists_boundedContinuous_bobkov_integrand`, `BooleanAnalysis.GaussianSpace.tendsto_integral_normalizedBoolBlocks`, `BooleanAnalysis.GaussianSpace.tendsto_block_gradient_error`, `BooleanAnalysis.GaussianSpace.continuous_closedGaussianProfile`, `BooleanAnalysis.GaussianSpace.bobkov_normalizedBoolBlocks_le`.
