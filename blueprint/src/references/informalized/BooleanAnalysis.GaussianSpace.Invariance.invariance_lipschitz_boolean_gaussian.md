<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceTruncation.lean :: BooleanAnalysis.GaussianSpace.Invariance.invariance_lipschitz_boolean_gaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Boolean-to-Gaussian Invariance

**Claim.** There is a positive constant $K$ such that every Boolean function satisfying the stated degree, variance, and influence bounds has the claimed expectation comparison with its Gaussian multilinear extension for every nonnegative Lipschitz constant and corresponding Lipschitz test function.

**Proof.** Take the positive constant $K$ supplied by the general invariance theorem (`invariance_lipschitz`). Use as the first probability space the Boolean cube with its uniform product measure, and as the second the product of standard Gaussian measures. The standard Gaussian law is a probability measure, as supplied by the standard-Gaussian moment fact (`hasInvarianceMoments_standardGaussian`). Each Boolean coordinate sign has the required invariance moments (`hasInvarianceMoments_uniformBoolCoordinate`), and each Gaussian coordinate has them as well (`hasInvarianceMoments_gaussianCoordinate`). The coordinates are independent in both product spaces. Apply the general invariance theorem to the Fourier coefficient polynomial of $f$, using the assumed degree, variance, and influence bounds. Its polynomial evaluation on Boolean signs equals $f$ by the Walsh expansion (`walsh_expansion`), equivalently the evaluation identity (`eval_fourierCoeff`). Finally, integration over the uniform Boolean product measure is the cube expectation (`integral_uniformBool_pi_eq_expect`), while the Gaussian product integral is the one in the assertion. Substituting these identifications gives the required bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasInvarianceMoments_standardGaussian`, `BooleanAnalysis.GaussianSpace.hasInvarianceMoments_uniformBoolCoordinate`, `BooleanAnalysis.GaussianSpace.hasInvarianceMoments_gaussianCoordinate`, `BooleanAnalysis.GaussianSpace.invariance_lipschitz`, `BooleanAnalysis.walsh_expansion`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_fourierCoeff`, `BooleanAnalysis.GaussianSpace.integral_uniformBool_pi_eq_expect`.
