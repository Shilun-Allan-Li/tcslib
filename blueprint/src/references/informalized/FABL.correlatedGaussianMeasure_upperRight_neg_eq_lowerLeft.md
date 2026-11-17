<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.correlatedGaussianMeasure_upperRight_neg_eq_lowerLeft -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian quadrant symmetry

**Claim.** For $\rho\in[-1,1]$ and $t\in\mathbb R$, the probability that both coordinates exceed $-t$ equals the probability that both are at most $t$.

**Proof.** Let $\mu$ be the correlated Gaussian measure. Its invariance under simultaneous negation (`correlatedGaussianMeasure_map_neg_biasedMajority`) implies that the measure of the upper-right quadrant above $-t$ equals the measure of its preimage under negation. That preimage is the open lower-left quadrant where both coordinates are strictly less than $t$. The desired event, where both coordinates are at most $t$, contains this open quadrant. Their difference is contained in the union of the two threshold lines, where the first or second coordinate equals $t$. These lines have total $\mu$-measure zero by `correlatedGaussianMeasure_coordinateThresholds_null`. Thus the open and closed lower-left regions agree up to a null set, and their probabilities are equal. The upper-right quadrant is open (`isOpen_gaussianUpperRightQuadrant`), ensuring its measure behaves under the mapped-measure identity used here.

**Key facts.** `FABL.correlatedGaussianMeasure_map_neg_biasedMajority`, `FABL.isOpen_gaussianUpperRightQuadrant`, `FABL.correlatedGaussianMeasure_coordinateThresholds_null`.
