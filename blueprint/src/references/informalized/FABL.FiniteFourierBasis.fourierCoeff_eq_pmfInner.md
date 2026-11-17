<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.FiniteFourierBasis.fourierCoeff_eq_pmfInner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients as inner products

**Claim.** The Fourier coefficient of a function at a multi-index equals its inner product, under the product probability measure, with the corresponding product basis function.

**Proof.** The Fourier coefficient is defined as the expectation of the function times the product basis function. The weighted inner product is exactly this expectation (\texttt{pmfInner_eq_expect}); substituting that expression gives the claimed equality.

**Key facts.** `FABL.pmfInner_eq_expect`.
