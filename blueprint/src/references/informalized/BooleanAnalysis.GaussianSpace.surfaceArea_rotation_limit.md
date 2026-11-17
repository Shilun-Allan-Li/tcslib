<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SurfaceArea.lean :: BooleanAnalysis.GaussianSpace.surfaceArea_rotation_limit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rotation Quotient Converges to Surface Area

**Claim.** For a measurable set, the scaled rotation-sensitivity quotient converges from the right at zero to its Gaussian surface area.

**Proof.** By definition, the Gaussian surface area is the lower limit of the scaled quotient as the angle approaches zero from above. Thus the lower-limit bound needed for convergence holds by equality. For the upper-limit bound, the scaled quotient is bounded above by the Gaussian surface area at every positive angle (`rotationSensitivity_quotient_le_surfaceArea`). The expression is also bounded on the right-neighborhood under consideration, so the upper-limit comparison applies. These lower- and upper-limit bounds force the limit to equal the surface area.

**Key facts.** `BooleanAnalysis.GaussianSpace.rotationSensitivity_quotient_le_surfaceArea`.
