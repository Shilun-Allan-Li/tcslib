<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.normalizedCorrelatedSignSumMeasure_disagreement_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of Disagreement Probabilities

**Claim.** For fixed $\rho\in[-1,1]$, the probability that the normalized correlated sign sum lies in the disagreement region converges to the corresponding probability for the correlated Gaussian measure.

**Proof.** The normalized correlated sign sum measures converge weakly to the correlated Gaussian measure (`normalizedCorrelatedSignSumMeasure_tendsto_correlatedGaussian`). The boundary of the disagreement region has measure zero under that Gaussian law (`correlatedGaussianMeasure_frontier_disagreement_null`). The Portmanteau theorem for weak convergence therefore gives convergence of the measures of this region: for a set whose boundary has zero limit measure, its probabilities converge. Applying that result yields the stated convergence.

**Key facts.** `FABL.normalizedCorrelatedSignSumMeasure_tendsto_correlatedGaussian`, `FABL.correlatedGaussianMeasure_frontier_disagreement_null`.
