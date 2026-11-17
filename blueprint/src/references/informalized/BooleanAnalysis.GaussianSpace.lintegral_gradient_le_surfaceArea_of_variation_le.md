<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SurfaceArea.lean :: BooleanAnalysis.GaussianSpace.lintegral_gradient_le_surfaceArea_of_variation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gradient bound by Gaussian surface area

**Claim.** Under the stated hypotheses, the Gaussian integral of the norm of the gradient, expressed as the square root of the sum of its squared coordinate values, is at most the Gaussian surface area of $A$.

**Proof.** Apply the gradient-from-variation bound (`lintegral_gaussianGradient_le_of_integral_variation_le`) with the variation estimate supplied by the hypotheses. For each positive angle $\theta$, the assumed bound controls the integral of $|f(X)-f(\cos\theta X+\sin\theta Y)|$. Reversing the order inside the absolute value does not change this integral. Multiplying the resulting bound by the nonnegative factor $\sqrt{\pi/2}$ and dividing by $\theta>0$ shows that the scaled variation is at most $\sqrt{\pi/2}\,\mathrm{rotationSensitivity}(A,\theta)/\theta$. The definition of Gaussian surface area as the limit inferior of these scaled sensitivities, together with the rotation-sensitivity-to-surface-area bound (`rotationSensitivity_le_surfaceArea`), supplies the constant required by the gradient-from-variation result. That result gives the claimed gradient integral bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.lintegral_gaussianGradient_le_of_integral_variation_le`, `BooleanAnalysis.GaussianSpace.rotationSensitivity_le_surfaceArea`.
