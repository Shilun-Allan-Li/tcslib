<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.affineKhintchineKahane -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Khintchine–Kahane Inequality

**Claim.** For every constant term $a_0$ and coefficient vector $a$, the uniform $L^1$ norm of the affine form is at least its uniform $L^2$ norm divided by $\sqrt{2}$.

**Proof.** Adjoin a new Rademacher coordinate and homogenize the affine form, turning its constant term into the coefficient of that coordinate. Apply the Khintchine–Kahane inequality to the resulting coefficient vector (FABL.khintchineKahane). For real coefficients, the Rademacher norm is the absolute value of the corresponding linear form (FABL.rademacherNorm_real_eq_abs_linearForm), so the inequality becomes the lower bound of the homogenized $L^1$ norm by the homogenized $L^2$ norm divided by $\sqrt{2}$. The uniform $L^2$ norm is the square root of the expected square (FABL.uniformLpNorm_two_eq_sqrt_expect_sq). The homogenized affine form has the same uniform $L^1$ and $L^2$ norms as the original affine form (FABL.uniformLpNorm_one_homogenizedAffineLinearForm; FABL.uniformLpNorm_two_homogenizedAffineLinearForm). Substituting these identities proves the result.

**Key facts.** `FABL.khintchineKahane`, `FABL.rademacherNorm_real_eq_abs_linearForm`, `FABL.uniformLpNorm_two_eq_sqrt_expect_sq`, `FABL.uniformLpNorm_one_homogenizedAffineLinearForm`, `FABL.uniformLpNorm_two_homogenizedAffineLinearForm`.
