<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlatedGaussianMeasure_coordinateAxes_null -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Axes Have Measure Zero

**Claim.** For $-1\leq\rho\leq1$, the correlated Gaussian measure assigns measure zero to the set where either coordinate is zero.

**Proof.** The set in question is the union of the two coordinate-zero sets, so it suffices to show that each has measure zero. For either coordinate, the measure of its zero set equals the measure of the singleton $\{0\}$ under the corresponding coordinate marginal: this follows from the measure-of-a-preimage formula for a measurable map. The first and second coordinate marginals are both standard Gaussian, by `correlatedGaussianMeasure_map_firstCoordinate` and `correlatedGaussianMeasure_map_secondCoordinate ρ hρ`. A standard Gaussian has no atoms, so each singleton has measure zero. The union of these two null sets is null.

**Key facts.** `FABL.correlatedGaussianMeasure_map_firstCoordinate`, `FABL.correlatedGaussianMeasure_map_secondCoordinate`.
