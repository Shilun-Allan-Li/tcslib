<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.functionNumericalDegree_fourierSubstitution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree under Fourier substitution

**Claim.** The numerical degree of the function obtained by substituting the coordinatewise sign encoding of a binary input into $p$ equals the Fourier degree of $p$.

**Proof.** The numerical coefficient family of the substituted function is the Fourier coefficient family of $p$ in the corresponding numerical representation (`numericalCoeff_fourierSubstitution`). The numerical degree of that coefficient family equals the Fourier degree of $p$ (`numericalDegree_fourierSubstitutionCoeff`). Combining these identifications gives the claimed equality.

**Key facts.** `FABL.numericalCoeff_fourierSubstitution`, `FABL.numericalDegree_fourierSubstitutionCoeff`.
