<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussian_projection_pair_law -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Law of Gaussian projections

**Claim.** If $a,b$ are unit vectors with inner product $\rho$, the pair of their projections of a standard Gaussian vector has the same law as $(X,\rho X+\sqrt{1-\rho^2}Y)$ for independent standard Gaussians $X,Y$.

**Proof.** Represent the two projections as continuous linear functionals $A$ and $B$ on the Gaussian vector, and represent the proposed pair as the continuous linear map $C(x,y)=(x,\rho x+\sqrt{1-\rho^2}y)$. It suffices to show that the image measures under these maps agree. The proof does this by comparing characteristic functions on every continuous linear functional of the target. The characteristic function of a standard Gaussian product measure is the exponential of minus one half the sum of squared coefficients (`charFunDual_gaussianPi`); for a standard one-dimensional Gaussian it is the corresponding exponential of minus one half the square (`charFunDual_standardGaussian`). A linear functional on $\mathbb R^2$ is determined by its values on the coordinate vectors (`realLinearFunctional_pair`). Expanding the sum of squared projection coefficients gives the squared norm in terms of the two vector norms and their inner product (`sum_sq_projectionCoefficients`). Substituting the hypotheses that the norms are one and the inner product is $\rho$, and using $(\sqrt{1-\rho^2})^2=1-\rho^2$, shows that the exponents in the two characteristic functions coincide. Hence the characteristic functions, and therefore the image measures, agree.

**Key facts.** `BooleanAnalysis.GaussianSpace.charFunDual_gaussianPi`, `BooleanAnalysis.GaussianSpace.charFunDual_standardGaussian`, `BooleanAnalysis.GaussianSpace.realLinearFunctional_pair`, `BooleanAnalysis.GaussianSpace.sum_sq_projectionCoefficients`.
