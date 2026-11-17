<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Kernel.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_compose_stronglyMeasurable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Gaussian Noise Operators

**Claim.** For $\rho,\sigma\in[-1,1]$ and integrable, strongly measurable $f$, applying Gaussian noise at parameter $\sigma$ and then at parameter $\rho$ agrees almost everywhere with applying it once at parameter $\rho\sigma$.

**Proof.** For almost every first input $x$, the full iterated integrand is integrable over the two Gaussian noise variables; this follows from $\texttt{integrable_gaussianNoise_compose_integrand}$. Fubini's theorem then writes the iterated noise as an integral over the product of two independent Gaussian vectors. Expanding the affine argument, the coefficient of $x$ is $\rho\sigma$, while the two independent noise terms have coefficients $\sigma\sqrt{1-\rho^2}$ and $\sqrt{1-\sigma^2}$. The integral of a function of this affine combination equals its integral against a single Gaussian vector with noise coefficient $\sqrt{1-(\rho\sigma)^2}$, by the Gaussian affine-pair identity ($\texttt{integral_gaussian_affine_pair}$). Its hypotheses hold because both square-root coefficients are nonnegative and their squared sum equals $1-(\rho\sigma)^2$; the latter equality is $\texttt{gaussianNoise_increment_variance}$. This gives the single noise application at parameter $\rho\sigma$ for almost every $x$, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_gaussianNoise_compose_integrand`, `BooleanAnalysis.GaussianSpace.integral_gaussian_affine_pair`, `BooleanAnalysis.GaussianSpace.gaussianNoise_increment_variance`.
