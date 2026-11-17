<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.numericalCoeff_fourierToF₂Polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients of the Normalized Fourier Transform

**Claim.** The numerical coefficient function of the normalized Fourier-to-binary-cube polynomial equals the explicitly defined coefficient function.

**Proof.** Use injectivity of numerical evaluation (`FABL.numericalEval_injective`), reducing equality of coefficient functions to equality of their evaluated functions. The numerical coefficients of the normalized polynomial evaluate to that polynomial (`FABL.numericalEval_numericalCoeff`), and the explicit coefficient function also evaluates to the same polynomial (`FABL.numericalEval_fourierToF₂Coeff`). Therefore the coefficient functions agree.

**Key facts.** `FABL.numericalEval_injective`, `FABL.numericalEval_numericalCoeff`, `FABL.numericalEval_fourierToF₂Coeff`.
