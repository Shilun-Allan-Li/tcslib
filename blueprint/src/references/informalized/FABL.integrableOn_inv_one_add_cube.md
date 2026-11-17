<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integrableOn_inv_one_add_cube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Reciprocal Cubic

**Claim.** The function $t\mapsto (1+t^3)^{-1}$ is integrable on $(0,\infty)$.

**Proof.** On $t>0$, the reciprocal cubic is bounded above by $2(1+t^2)^{-1}$. The latter is integrable on $(0,\infty)$, since the reciprocal quadratic has an integrable tail there. The reciprocal cubic is measurable and nonnegative on this interval, so comparison gives the claimed integrability.

**Key facts.** `FABL.inv_one_add_cube_le_two_mul_inv_one_add_sq`.
