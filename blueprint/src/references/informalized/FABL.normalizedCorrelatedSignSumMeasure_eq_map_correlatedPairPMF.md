<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.normalizedCorrelatedSignSumMeasure_eq_map_correlatedPairPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Normalized Sum Distributions

**Claim.** For $\rho\in[-1,1]$ and natural number $n$, the measure of the normalized sum of $n$ independent correlated sign pairs equals the distribution of the normalized pair sum generated from a uniform first sign vector and its coordinatewise noisy second vector.

**Proof.** Write the measure of the normalized sum as the pushforward, under summation and scaling by $(\sqrt n)^{-1}$, of the product of the $n$ single-pair measures pushed forward by the map sending each sign pair to its point in the plane. The product-measure pushforward identity `Measure.pi_map_pi` identifies this with the pushforward of the product measure on the $n$ sign pairs, followed by the coordinate map. The map-composition rule for measures (`Measure.map_map`) combines these two successive pushforwards. By `independentProductPMF_toMeasure`, the product of the single-pair measures is the measure associated with the independent product PMF. The coordinate representation theorem (`correlatedPairPMF_map_pairCoordinatesEquiv`) identifies that PMF with the image of the correlated pair-vector PMF under the coordinate equivalence. Pushing its associated measure forward is compatible with mapping a PMF (`PMF.toMeasure_map`); composing the coordinate equivalence with the sum map gives exactly the normalized pair-sum map. Hence the two measures agree.

**Key facts.** `FABL.independentProductPMF_toMeasure`, `FABL.correlatedPairPMF_map_pairCoordinatesEquiv`.
