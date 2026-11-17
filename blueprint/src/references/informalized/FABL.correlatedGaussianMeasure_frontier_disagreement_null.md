<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlatedGaussianMeasure_frontier_disagreement_null -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disagreement Boundary Has Measure Zero

**Claim.** For $-1\leq\rho\leq1$, the boundary of the disagreement region has measure zero under the correlated Gaussian measure.

**Proof.** The boundary of the disagreement region is contained in the union of the two coordinate axes, by `frontier_gaussianDisagreementRegion_subset`. The measure of that union is zero by `correlatedGaussianMeasure_coordinateAxes_null ρ hρ`. Monotonicity of measure on null sets then gives measure zero for the boundary.

**Key facts.** `FABL.frontier_gaussianDisagreementRegion_subset`, `FABL.correlatedGaussianMeasure_coordinateAxes_null`.
