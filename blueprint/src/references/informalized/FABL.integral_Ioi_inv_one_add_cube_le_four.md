<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_Ioi_inv_one_add_cube_le_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Reciprocal Integral Bound

**Claim.** The integral of $(1+t^3)^{-1}$ over $t>0$ is at most $4$.

**Proof.** For every $t\ge 0$, compare the integrand with $2(1+t^2)^{-1}$ using the pointwise bound `inv_one_add_cube_le_two_mul_inv_one_add_sq`. Both functions are integrable on the positive half-line, so monotonicity of the integral bounds the desired integral by the integral of this majorant. The latter is $2\int_0^\infty(1+t^2)^{-1}\,dt=\pi$, by the antiderivative $\arctan t$. Finally, $\pi\le 4$.

**Key facts.** `FABL.integrableOn_inv_one_add_cube`, `FABL.inv_one_add_cube_le_two_mul_inv_one_add_sq`.
