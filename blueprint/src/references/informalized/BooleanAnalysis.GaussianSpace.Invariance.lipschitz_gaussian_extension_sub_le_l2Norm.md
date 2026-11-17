<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Perturbation.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_gaussian_extension_sub_le_l2Norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Extension Stability

**Claim.** For Boolean functions $f,g$ and a $c$-Lipschitz function $\psi$, the expectations of $\psi$ applied to their Gaussian multilinear extensions differ by at most $c\|f-g\|_2$.

**Proof.** Take the coordinate functions on $\mathbb R^n$ with the product standard Gaussian measure. Each coordinate has finite fourth moment, mean zero, and second moment one (\texttt{hasInvarianceMoments_gaussianCoordinate}); the one-dimensional standard Gaussian is a probability measure by \texttt{hasInvarianceMoments_standardGaussian}. Product-measure independence makes these coordinates independent. Apply the Lipschitz stability estimate for multilinear random polynomials (\texttt{lipschitz_polynomial_integral_sub_le}) to the Fourier coefficient families of $f$ and $g$. The polynomial represented by the difference of those families is the difference of the two extensions (\texttt{eval_sub}), and each Fourier coefficient family evaluates on the Boolean cube to its original function (\texttt{eval_fourierCoeff}). Consequently the polynomial $L^2$ bound in that estimate is precisely $\|f-g\|_2$, giving the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasInvarianceMoments_standardGaussian`, `BooleanAnalysis.GaussianSpace.Invariance.hasInvarianceMoments_gaussianCoordinate`, `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_polynomial_integral_sub_le`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_sub`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_fourierCoeff`.
