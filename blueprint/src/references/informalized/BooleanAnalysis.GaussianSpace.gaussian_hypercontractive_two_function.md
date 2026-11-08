<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussian_hypercontractive_two_function -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-function Gaussian hypercontractivity

**Claim.** For nonnegative $r,s$ with $rs\le1$ and $0\le\rho\le1$ with $\rho^2\le rs$, the correlated Gaussian product is integrable and its absolute integral is at most the product of the indicated Gaussian $L^{1+r}$ and $L^{1+s}$ norms.

**Proof.** The assumptions $r,s\ge0$ ensure both exponents are at least one. If $\rho=0$, the correlated Gaussian measure is the product of the two standard Gaussian measures. The two functions are integrable in their respective marginal spaces, so their product is integrable on the product space and its integral factors. Applying the bound of the absolute mean by the corresponding $L^p$ norm to each factor proves the desired estimate. If $\rho\ne0$, the constraints imply $r,s>0$. The two marginals of the correlated Gaussian measure are standard Gaussian, so the positive-offset two-function inequality applies: it gives integrability and bounds the integral of $|f(z_1)||g(z_2)|$ by the product of the stated norms. The absolute value of the integral of $f(z_1)g(z_2)$ is at most that integral of the absolute value, yielding the conclusion.

**Key facts.** `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_zero`, `BooleanAnalysis.GaussianSpace.norm_integral_le_toReal_eLpNorm`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_fst`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_snd`, `BooleanAnalysis.GaussianSpace.gaussian_two_function_positiveOffsets`.
