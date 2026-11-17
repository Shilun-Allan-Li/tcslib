<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.correlatedGaussianMeasure_frontier_upperRight_null -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Right Quadrant Boundary Has Measure Zero

**Claim.** For $-1\leq\rho\leq1$ and $t\in\mathbb R$, the boundary of the set where both coordinates exceed $t$ has measure zero under the correlated Gaussian measure.

**Proof.** The boundary of the upper right quadrant is contained in the union of the two coordinate threshold sets at $t$, by `frontier_gaussianUpperRightQuadrant_subset`. That union has measure zero by `correlatedGaussianMeasure_coordinateThresholds_null ρ hρ t`. Since a subset of a null set is null, the boundary has measure zero.

**Key facts.** `FABL.frontier_gaussianUpperRightQuadrant_subset`, `FABL.correlatedGaussianMeasure_coordinateThresholds_null`.
