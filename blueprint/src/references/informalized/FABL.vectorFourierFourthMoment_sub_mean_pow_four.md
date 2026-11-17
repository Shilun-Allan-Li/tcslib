<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/FourierFourthMoment.lean :: FABL.vectorFourierFourthMoment_sub_mean_pow_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Moment Excluding the Mean Coefficient

**Claim.** The vector Fourier fourth moment minus the fourth power of the mean equals the sum of the fourth powers of the coefficients at all nonzero indices.

**Proof.** Expand the fourth moment as the sum over all cube indices, and replace the zero-index coefficient by the mean using `FABL.vectorFourierCoeff_zero_eq_mean`. The desired sum is the same full sum with the zero index removed, since filtering out zero is equivalent to erasing it from the cube. Splitting the full sum into the contribution at zero and the sum over the remaining indices, then subtracting the zero contribution, gives the claimed identity.

**Key facts.** `FABL.vectorFourierCoeff_zero_eq_mean`.
