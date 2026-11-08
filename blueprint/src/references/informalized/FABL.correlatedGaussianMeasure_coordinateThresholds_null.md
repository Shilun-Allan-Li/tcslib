<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.correlatedGaussianMeasure_coordinateThresholds_null -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Thresholds Have Measure Zero

**Claim.** For $-1\leq\rho\leq1$ and $t\in\mathbb R$, the correlated Gaussian measure assigns measure zero to the set where either coordinate equals $t$.

**Proof.** Split the union into the two threshold sets. For each coordinate, its threshold set is the preimage of the singleton $\{t\}$ under that coordinate map. The measure-of-a-preimage formula identifies its measure with the measure of $\{t\}$ under the corresponding coordinate marginal. Both marginals are standard Gaussian, by `correlatedGaussianMeasure_map_firstCoordinate` and `correlatedGaussianMeasure_map_secondCoordinate ρ hρ`. Since the standard Gaussian has no atoms, both threshold sets have measure zero, and hence so does their union.

**Key facts.** `FABL.correlatedGaussianMeasure_map_firstCoordinate`, `FABL.correlatedGaussianMeasure_map_secondCoordinate`.
