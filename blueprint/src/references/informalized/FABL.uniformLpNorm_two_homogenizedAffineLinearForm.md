<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.uniformLpNorm_two_homogenizedAffineLinearForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogenized Affine Form Norm

**Claim.** The uniform $L^2$ norm of the linear form on the $(n+1)$-dimensional sign cube with coefficients $(a_0,a_1,\ldots,a_n)$ equals the uniform $L^2$ norm of the affine form $a_0+\sum_{i=1}^n a_i x_i$ on the $n$-dimensional sign cube.

**Proof.** Apply the second-moment formula for the uniform $L^2$ norm to each side. The expected squares of the homogenized linear form and the affine form are equal by `expect_sq_homogenizedAffineLinearForm`. Thus their square roots, and hence their uniform $L^2$ norms, are equal.

**Key facts.** `FABL.uniformLpNorm_two_eq_sqrt_expect_sq`, `FABL.expect_sq_homogenizedAffineLinearForm`.
