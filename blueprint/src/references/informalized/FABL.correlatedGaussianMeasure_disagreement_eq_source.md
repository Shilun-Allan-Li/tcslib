<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlatedGaussianMeasure_disagreement_eq_source -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disagreement Probability via the Source Pair

**Claim.** The correlated Gaussian measure of the disagreement region equals the probability, for two independent standard Gaussian variables, that their image under the correlation map lies in that region.

**Proof.** By definition, the correlated Gaussian measure is the product standard Gaussian measure pushed forward by the correlation map. The disagreement region is measurable because it is open (`isOpen_gaussianDisagreementRegion`). The measure-of-a-preimage formula for a measurable map therefore identifies its measure under the pushforward with the product Gaussian measure of its preimage. Unfolding the correlation map and the disagreement region shows that this preimage is exactly the source disagreement set.

**Key facts.** `FABL.continuous_gaussianCorrelationMap`, `FABL.isOpen_gaussianDisagreementRegion`.
