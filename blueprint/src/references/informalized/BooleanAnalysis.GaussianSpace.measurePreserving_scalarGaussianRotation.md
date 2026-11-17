<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianRotation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rotation invariance of two Gaussian variables

**Claim.** For every $\theta\in\mathbb R$, the planar rotation by $\theta$ preserves the product of two standard Gaussian measures.

**Proof.** The standard Gaussian measure is a Gaussian measure, and the product of two copies is the corresponding standard Gaussian measure on the plane. A planar rotation leaves this Gaussian measure unchanged (`IsGaussian.map_rotation_eq_self`). The rotation is measurable, so the measure-preserving property follows.
