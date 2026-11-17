<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.contDiff_integral_gaussian_exp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Smoothness of a Gaussian exponential integral

**Claim.** If $f$ is integrable with respect to standard Gaussian measure, then integrating $f(y)$ against the stated Gaussian exponential kernel gives a function of $x$ that is smooth of every order.

**Proof.** First take the Gaussian Fourier integral of $f$, with frequency parameter $b$. It is continuous, and its absolute value is bounded uniformly in the frequency by the integral of $|f|$. Apply the smoothness result for Gaussian Fourier integrals to this bounded Fourier transform, now with parameter $a$. This gives a smooth complex-valued function of $x$. Taking its real part preserves smoothness. The Gaussian double-phase identity identifies that real part pointwise with the given integral: the two Fourier phases combine into the exponential kernel in the statement. Therefore the original real-valued function is smooth of every order.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuous_gaussianFourierIntegral`, `BooleanAnalysis.GaussianSpace.contDiff_gaussianFourierIntegral`, `BooleanAnalysis.GaussianSpace.integral_gaussian_double_phase`.
