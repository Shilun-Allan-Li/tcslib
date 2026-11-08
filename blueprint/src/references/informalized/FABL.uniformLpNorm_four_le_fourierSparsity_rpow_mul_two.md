<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HomogeneousMoments.lean :: FABL.uniformLpNorm_four_le_fourierSparsity_rpow_mul_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Norm from Fourier Sparsity

**Claim.** For a function on the Boolean cube, its uniform $L^4$ norm is at most the fourth root of its Fourier sparsity times its uniform $L^2$ norm.

**Proof.** It is enough to prove the inequality after taking fourth powers, because both sides are nonnegative. The fourth-power identity converts the left side to the fourth moment, while the factor involving Fourier sparsity has fourth power equal to the sparsity itself. Also, the square of the uniform $L^2$ norm is the second moment (`FABL.uniformLpNorm_two_sq_eq_expect_sq`). The remaining inequality is precisely the fourth-moment bound by Fourier sparsity times the square of the second moment (`FABL.fourthMoment_le_fourierSparsity_mul_secondMoment_sq`). Applying these identities gives the fourth-power inequality, and monotonicity of the fourth power on nonnegative reals yields the claimed norm bound.

**Key facts.** `FABL.uniformLpNorm_four_pow_eq_expect_fourth`, `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_two_sq_eq_expect_sq`, `FABL.fourthMoment_le_fourierSparsity_mul_secondMoment_sq`.
