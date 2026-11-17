<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.halfspace_rotation_quotient_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halfspace rotation limit

**Claim.** For a unit normal vector $a$ and threshold $t$, the scaled rotation sensitivity of the halfspace with normal $a$ tends, as the rotation angle approaches zero from above, to the standard Gaussian density at $t$.

**Proof.** The halfspace rotation identity (`rotationSensitivity_halfspace_eq_scalar`) says that its rotation sensitivity equals the scalar Gaussian disagreement probability for the threshold $t$. Substitute this identity into the scaled quotient. The resulting expression is exactly the scalar rotation disagreement quotient, whose right-hand limit is the standard Gaussian density at $t$ (`scalar_rotation_disagreement_quotient_tendsto`).

**Key facts.** `BooleanAnalysis.GaussianSpace.rotationSensitivity_halfspace_eq_scalar`, `BooleanAnalysis.GaussianSpace.scalar_rotation_disagreement_quotient_tendsto`.
