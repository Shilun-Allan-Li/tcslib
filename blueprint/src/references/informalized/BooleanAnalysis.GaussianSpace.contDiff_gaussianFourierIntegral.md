<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.contDiff_gaussianFourierIntegral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Smoothness of the Gaussian Fourier integral

**Claim.** For a strongly measurable, globally bounded complex function on Gaussian space, its Gaussian Fourier integral is infinitely continuously differentiable as a function of the frequency variable.

**Proof.** Rewrite the displayed integral as the vector Fourier integral associated with the Gaussian pairing. The vector Fourier smoothness theorem says that this Fourier integral is infinitely continuously differentiable once, for each order $k$, the integrand has an integrable bound after multiplication by the $k$th power of the norm of the integration variable. Here the integrand is bounded in absolute value by $\|t\|^k C$: the exponential has norm one, and $\|H(t)\|\le C$. The Gaussian moment bound guarantees that $\|t\|^k$ is integrable, so this estimate supplies the required domination at every order. Thus the Fourier integral, and hence the original integral, is smooth of every order.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianFourierIntegral_eq`, `BooleanAnalysis.GaussianSpace.integrable_gaussianPi_norm_pow`.
