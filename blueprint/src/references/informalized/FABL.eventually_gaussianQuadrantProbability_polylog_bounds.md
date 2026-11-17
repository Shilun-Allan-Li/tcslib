<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.eventually_gaussianQuadrantProbability_polylog_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Quadrant Probability Bounds

**Claim.** Fix a correlation parameter $\rho\in(0,1)$. For all sufficiently small $\mu\in(0,1)$, the probability that two standard Gaussian coordinates with correlation $\rho$ both exceed the standard Gaussian upper-tail quantile at mass $\mu$ lies between the stated lower and upper bounds.

**Proof.** As $\mu$ tends to zero, its standard Gaussian upper-tail quantile tends to infinity. Thus, eventually the quantile is at least $1$. The upper-tail quantile identity says that the upper tail at this quantile equals $\mu$; equivalently, the upper-tail map evaluated at the quantile is exactly $\mu$. Apply the Gaussian quadrant lower-tail estimate at this threshold, using that it is at least $1$, and apply the corresponding upper-tail estimate at the same threshold. Replacing the upper-tail value by $\mu$ and the threshold by its quantile yields the two claimed bounds, with the stated constant and powers.

**Key facts.** `FABL.tendsto_standardGaussianUpperQuantile_atBot`, `FABL.standardGaussianUpperTail_quantile`, `FABL.gaussianQuadrantAtThreshold_lower_tail_rpow_div_quantilePower`, `FABL.gaussianQuadrantAtThreshold_le_tail_rpow`.
