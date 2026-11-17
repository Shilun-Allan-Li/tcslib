<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_abs_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute First Moment of a Standard Gaussian

**Claim.** The absolute first moment of a standard Gaussian is $\sqrt{2/\pi}$.

**Proof.** The standard Gaussian has an integrable identity function, so its absolute moment can be expressed as twice the integral of the positive part minus the integral of the identity. The identity integral is zero because this Gaussian is centered. Its positive-part integral is $(2\pi)^{-1/2}$ (`integral_posPart_standardGaussian`). Thus the absolute moment is $2(2\pi)^{-1/2}$, which simplifies to $\sqrt{2/\pi}$ (`two_mul_inv_sqrt_two_mul_pi`).

**Key facts.** `FABL.integral_posPart_standardGaussian`, `FABL.two_mul_inv_sqrt_two_mul_pi`.
