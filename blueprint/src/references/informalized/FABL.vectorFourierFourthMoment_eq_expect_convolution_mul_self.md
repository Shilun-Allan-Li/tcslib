<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/FourierFourthMoment.lean :: FABL.vectorFourierFourthMoment_eq_expect_convolution_mul_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Fourier Moment and Convolution

**Claim.** The sum of the fourth powers of the vector Fourier coefficients of $f$ equals $\mathbb{E}_t[(f*f)(t)^2]$.

**Proof.** For each frequency, the Fourier coefficient of the self-convolution is the square of the Fourier coefficient of $f$ (`FABL.vectorFourierCoeff_convolution`). Therefore the sum of the products of the self-convolution's coefficients with themselves is the sum of the fourth powers of the coefficients of $f$. Plancherel's identity (`FABL.vector_plancherel`), applied to the self-convolution with itself, identifies this sum with the average of its pointwise square, as required.

**Key facts.** `FABL.vectorFourierCoeff_convolution`, `FABL.vector_plancherel`.
