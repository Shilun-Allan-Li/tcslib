<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.fourierToF₂Coeff_booleanFunction_eq_intCast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer formula for transformed coefficients

**Claim.** For a sign-valued function, each transformed Fourier coefficient equals, as a real number, the integer alternating sum over subsets in the stated formula.

**Proof.** First identify the transformed coefficient with the numerical coefficient of the polynomial obtained by applying the Fourier-to-bit transformation (`numericalCoeff_fourierToF₂Polynomial`). For a sign-valued function, that transformed polynomial equals the real embedding of its bit-encoded Boolean function (`fourierToF₂Polynomial_booleanFunction`). Finally, the numerical coefficient of this real embedding is the integer-valued alternating subset sum, viewed in the reals (`numericalCoeff_booleanRealEmbedding_eq_intCast`). Chaining these equalities gives the formula.

**Key facts.** `FABL.numericalCoeff_fourierToF₂Polynomial`, `FABL.fourierToF₂Polynomial_booleanFunction`, `FABL.numericalCoeff_booleanRealEmbedding_eq_intCast`.
