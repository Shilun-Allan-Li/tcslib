<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of the zero function

**Claim.** The Fourier coefficient of the zero function at every multi-index is zero.

**Proof.** In the defining expectation, the integrand is pointwise zero because the function being evaluated is zero. The expectation of the constant-zero function under a probability mass function is zero (FABL.pmfExpectation_const), which proves the claim.

**Key facts.** `FABL.pmfExpectation_const`.
