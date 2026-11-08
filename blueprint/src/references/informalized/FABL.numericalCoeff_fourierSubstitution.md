<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.numericalCoeff_fourierSubstitution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficients After Fourier Substitution

**Claim.** The numerical coefficient function of the Fourier-substituted function is the coefficient function explicitly formed from the Fourier coefficients.

**Proof.** Apply injectivity of numerical evaluation (`FABL.numericalEval_injective`), so it suffices to show that the two coefficient functions have the same numerical evaluation. The evaluation of the numerical coefficient function of the substituted function is that substituted function itself (`FABL.numericalEval_numericalCoeff`). The explicitly defined coefficient function also evaluates to the substituted function (`FABL.numericalEval_fourierSubstitutionCoeff`). Since both evaluations agree, injectivity gives equality of the coefficient functions.

**Key facts.** `FABL.numericalEval_injective`, `FABL.numericalEval_numericalCoeff`, `FABL.numericalEval_fourierSubstitutionCoeff`.
