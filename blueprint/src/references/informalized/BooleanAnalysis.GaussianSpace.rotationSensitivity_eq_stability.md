<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Indicator.lean :: BooleanAnalysis.GaussianSpace.rotationSensitivity_eq_stability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rotation sensitivity and noise stability

**Claim.** For a measurable set and an angle in [0,π], its rotation sensitivity equals twice its Gaussian measure minus twice the noise stability of its indicator at correlation cos θ.

**Proof.** On the product Gaussian space, let E be the event that the first vector belongs to A, and F the event that its rotated vector belongs to A. The marginal Gaussian measure of E is the measure of A. The rotated vector also has standard Gaussian law: apply `measurePreserving_gaussianCombination` with coefficients cos θ and sin θ, whose squares sum to one and whose sine coefficient is nonnegative on the given angle range. Thus F has the same measure as E. The indicator noise-stability identity (`gaussianNoiseStability_indicator_measure`) identifies the noise stability with the measure of E∩F. By definition, rotation sensitivity is the measure of the symmetric difference of E and F. The measure identity for a symmetric difference, together with equality of the two marginal measures, gives μ(E△F)=2(μ(E)−μ(E∩F)), which is the asserted formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianNoiseStability_indicator_measure`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianCombination`.
