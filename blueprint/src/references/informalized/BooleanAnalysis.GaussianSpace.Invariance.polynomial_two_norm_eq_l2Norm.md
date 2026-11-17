<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Perturbation.lean :: BooleanAnalysis.GaussianSpace.Invariance.polynomial_two_norm_eq_l2Norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Norm Identity

**Claim.** The real-valued $L^2(\mu)$ norm of the random-input multilinear evaluation of $F$ equals the uniform $L^2$ norm of its Boolean-cube evaluation.

**Proof.** First, the random-input evaluation belongs to $L^2$, since its $L^4$ integrability follows from independence and the coordinate fourth-moment assumptions (`evalMultilinearRV_memLp`), and hence it also belongs to $L^2$. The norm-to-moment identity identifies the square of its real-valued $L^2$ norm with the integral of its square (`rvLpNorm_rpow`). The integral of that square is the sum of the squared coefficients, by the orthogonality of distinct multilinear monomials under independent, mean-zero, variance-one inputs (`MultilinearMoments.integral_eval_sq`). On the Boolean cube, the corresponding characters are orthonormal, so the uniform expectation of the squared polynomial is the same coefficient-square sum (`MultilinearPolynomial.expect_eval_sq`). Thus the squares of the two norms agree. Both norms are nonnegative, so taking their nonnegative square roots yields the claimed equality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp`, `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`, `BooleanAnalysis.Hypercontractivity.MultilinearMoments.integral_eval_sq`, `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.expect_eval_sq`.
