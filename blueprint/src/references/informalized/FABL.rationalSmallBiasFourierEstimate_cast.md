<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.rationalSmallBiasFourierEstimate_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Casting the Small-Bias Fourier Estimate

**Claim.** The rational empirical Fourier coefficient of the generated samples labeled by the target, regarded as a real number, equals the real sample Fourier estimate of the target on the specified coordinate set.

**Proof.** Write the rational estimate as the empirical Fourier coefficient of the generated cube samples labeled by the target. The rational-to-real empirical coefficient identity (`empiricalFourierCoeff_cast`) turns it into the real empirical Fourier coefficient. Unfolding that coefficient and the sample estimate shows that both are the average of the target's real value times the specified Fourier monomial over the same generated samples.

**Key facts.** `FABL.empiricalFourierCoeff_cast`.
