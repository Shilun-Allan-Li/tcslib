<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolBLR.lean :: BoolBLR.triple_expectation_eq_cube_fourier_aux_h_convolution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier expansion of self-convolution

**Claim.** The convolution of the sign lift of a Boolean function with itself is the sum of its squared Fourier coefficients times the corresponding Walsh characters.

**Proof.** Fix an input $x$. Apply the Fourier expansion theorem (`fourier_expansion`) to the convolution at $x$. Each Fourier coefficient of this convolution is the product of the corresponding coefficients of its two factors, by the convolution coefficient identity (`fourier_coeff_convolution`). Since both factors are the same sign lift, each product is the square of that coefficient, yielding the asserted expansion.

**Key facts.** `fourier_expansion`, `BoolFourier.fourier_coeff_convolution`.
