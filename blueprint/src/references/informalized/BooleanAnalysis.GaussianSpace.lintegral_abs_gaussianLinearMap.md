<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.lintegral_abs_gaussianLinearMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Gaussian moment of a linear map

**Claim.** For a continuous linear functional on $\mathbb R^n$, the nonnegative extended Gaussian integral of its absolute value equals the stated square-root-of-squared-coefficients expression times twice the standard Gaussian density at zero.

**Proof.** First, the functional is integrable under standard Gaussian measure (\texttt{BooleanAnalysis.GaussianSpace.integrable_gaussianLinearMap}), so its absolute value is integrable as well. For a nonnegative function, its integral embedded into the extended nonnegative reals equals the integral of its real-valued embedding. Apply this conversion to the absolute value, which is everywhere nonnegative, and then use the real-valued absolute Gaussian moment identity (\texttt{BooleanAnalysis.GaussianSpace.integral_abs_gaussianLinearMap}). This gives exactly the asserted extended-integral formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_gaussianLinearMap`, `BooleanAnalysis.GaussianSpace.integral_abs_gaussianLinearMap`.
