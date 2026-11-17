<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveNecessity.lean :: FABL.expect_sq_pos_of_uniformLpNorm_two_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive second moment from positive norm

**Claim.** If the uniform $L^2$ norm of $X$ on a finite type is positive, then its second moment is positive.

**Proof.** The square of the uniform $L^2$ norm equals the second moment (by `FABL.uniformLpNorm_two_sq_eq_expect_sq`). Since the norm is positive, its square is positive, and therefore the second moment is positive.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`.
