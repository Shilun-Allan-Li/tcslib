<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/RandomSmallBias.lean :: FABL.randomSmallBiasDensity_isBiased_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias of the empirical density

**Claim.** The random density formed from the samples is $\varepsilon$-biased exactly when every nonzero frequency has empirical character average of absolute value at most $\varepsilon$.

**Proof.** By definition, the density is $\varepsilon$-biased when, for each nonzero frequency, the absolute value of its vector Fourier coefficient is at most $\varepsilon$. The Fourier coefficient of the random density equals the empirical uniform average of the corresponding Walsh character (`vectorFourierCoeff_randomSmallBiasDensity`). Substituting this identity in each frequency condition gives precisely the defining condition for the sample to be small-biased. Since the equality holds for every frequency, the two conditions are equivalent.

**Key facts.** `FABL.vectorFourierCoeff_randomSmallBiasDensity`.
