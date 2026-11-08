<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Perturbation.lean :: BooleanAnalysis.GaussianSpace.Invariance.lipschitz_expect_sub_le_l2Norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz stability of cube expectation

**Claim.** For a $c$-Lipschitz function $\psi$, the difference between the uniform expectations of $\psi\circ f$ and $\psi\circ g$ is at most $c\|f-g\|_2$.

**Proof.** Represent $f$ and $g$ by their Fourier multilinear polynomials and evaluate those polynomials on the independent uniform sign coordinates of the Boolean cube. Each coordinate has mean zero and second moment one, and has a finite fourth moment; these are the required moment conditions. The Lipschitz polynomial integral inequality (`lipschitz_polynomial_integral_sub_le`) then bounds the difference of the two expectations by $c$ times the $L^2$ norm of the difference of the evaluated polynomials. The polynomial evaluations recover $f$ and $g$ (`eval_fourierCoeff`), and evaluation respects subtraction (`eval_sub`), so this norm is exactly $\|f-g\|_2$. The product integral is the uniform cube expectation (`integral_uniformBool_pi_eq_expect`), giving the asserted inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_polynomial_integral_sub_le`, `BooleanAnalysis.GaussianSpace.hasInvarianceMoments_uniformBoolCoordinate`, `BooleanAnalysis.GaussianSpace.integral_uniformBool_pi_eq_expect`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_fourierCoeff`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_sub`.
