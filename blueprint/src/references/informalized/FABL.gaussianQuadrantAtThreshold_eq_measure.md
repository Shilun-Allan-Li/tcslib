<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantAtThreshold_eq_measure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadrant Probability at a Threshold

**Claim.** For 0<ρ<1 and real t, the Gaussian quadrant probability at threshold t equals the correlated Gaussian measure of the upper-right quadrant above t.

**Proof.** Expand the definition of the threshold probability: it is the quadrant probability at correlation ρ with volume parameter given by the standard Gaussian upper tail at t. In the definition of quadrant probability, the threshold for that volume parameter is its upper quantile. The upper quantile of the upper tail at t is exactly t (standardGaussianUpperQuantile_upperTail). Substituting this identity identifies the set being measured with the upper-right quadrant above t, proving the equality.

**Key facts.** `FABL.standardGaussianUpperQuantile_upperTail`.
