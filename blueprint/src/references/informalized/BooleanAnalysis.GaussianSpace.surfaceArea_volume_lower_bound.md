<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SurfaceArea.lean :: BooleanAnalysis.GaussianSpace.surfaceArea_volume_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Surface Area Lower Bound from Gaussian Volume

**Claim.** If $A$ is measurable and has Gaussian measure $\alpha$, then $2\sqrt{2/\pi}\,\alpha(1-\alpha)$ is at most its Gaussian surface area.

**Proof.** Apply the general bound that the scaled rotation sensitivity at any positive angle is at most the Gaussian surface area (`rotationSensitivity_le_surfaceArea`), choosing the angle $\pi/2$. At this angle, the rotation sensitivity equals twice the Gaussian measure of $A$ times one minus that measure (`rotationSensitivity_pi_div_two`). Substitution gives the desired lower bound after simplifying the positive constants: $\sqrt{\pi/2}/(\pi/2)=\sqrt{2/\pi}$.

**Key facts.** `BooleanAnalysis.GaussianSpace.rotationSensitivity_le_surfaceArea`, `BooleanAnalysis.GaussianSpace.rotationSensitivity_pi_div_two`.
