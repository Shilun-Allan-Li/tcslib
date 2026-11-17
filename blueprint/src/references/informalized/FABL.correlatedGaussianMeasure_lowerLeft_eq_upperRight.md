<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianThresholds.lean :: FABL.correlatedGaussianMeasure_lowerLeft_eq_upperRight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Opposite Quadrant Probabilities Agree

**Claim.** For $-1\leq\rho\leq1$, the probability that both coordinates are nonpositive equals the probability that both are strictly positive.

**Proof.** The correlated Gaussian measure is invariant under simultaneous negation of both coordinates, by `correlatedGaussianMeasure_map_neg`. Apply this invariance to the lower-left quadrant: the measure of that quadrant equals the measure of its preimage under negation. Negation sends the lower-left quadrant exactly to the strictly upper right quadrant, as is seen by negating each coordinate inequality. Thus the two measures agree. Taking real-valued measures on both sides preserves the equality.

**Key facts.** `FABL.correlatedGaussianMeasure_map_neg`.
