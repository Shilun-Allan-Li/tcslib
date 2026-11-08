<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/FourierFourthMoment.lean :: FABL.vectorFourierFourthMoment_eq_additiveEnergy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Fourier Moment and Additive Energy

**Claim.** The sum of the fourth powers of the vector Fourier coefficients of $f$ equals $\mathbb{E}_{x,y,z}[f(x)f(y)f(z)f(x+y+z)]$.

**Proof.** First identify the fourth Fourier moment with the average of the square of the normalized self-convolution, using `FABL.vectorFourierFourthMoment_eq_expect_convolution_mul_self`. The self-convolution identity `FABL.expect_convolution_mul_self_eq_additiveEnergy` then expresses that average as the stated three-variable average. Combining the two identities proves the claim.

**Key facts.** `FABL.vectorFourierFourthMoment_eq_expect_convolution_mul_self`, `FABL.expect_convolution_mul_self_eq_additiveEnergy`.
