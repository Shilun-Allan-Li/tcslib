<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BiasedMajorityGaussianLimit.lean :: FABL.normalizedCorrelatedSignSumMeasure_upperRight_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of Upper-Right Quadrant Probabilities

**Claim.** For fixed $\rho\in[-1,1]$ and threshold $t$, the probability that the normalized correlated sign sum lies in the upper-right quadrant above $t$ converges to the probability of that region under the correlated Gaussian measure.

**Proof.** The normalized correlated sign sum measures converge weakly to the correlated Gaussian measure (`normalizedCorrelatedSignSumMeasure_tendsto_correlatedGaussian`). The frontier of the upper-right quadrant above $t$ has zero measure under that Gaussian law (`correlatedGaussianMeasure_frontier_upperRight_null`). The Portmanteau theorem for weak convergence then implies convergence of the probabilities of this region, because its boundary is null for the limiting measure.

**Key facts.** `FABL.normalizedCorrelatedSignSumMeasure_tendsto_correlatedGaussian`, `FABL.correlatedGaussianMeasure_frontier_upperRight_null`.
