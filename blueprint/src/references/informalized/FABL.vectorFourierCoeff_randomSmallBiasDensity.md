<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.vectorFourierCoeff_randomSmallBiasDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient of an empirical density

**Claim.** For a positive sample size and a list of cube samples, the vector Fourier coefficient of the empirical density at $\gamma$ equals the average of the Walsh character indexed by $\gamma$ over those samples.

**Proof.** Use the expectation representation of the vector Fourier coefficient. The empirical density is the uniform pushforward of the sample map, so its expectation against any function equals the average of that function evaluated on the samples. Converting this finite expectation into a sum divided by the sample size gives precisely the finite empirical mean of the Walsh character.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.ProbabilityDensity.expectation_uniformPushforward`.
