<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.functionNumericalDegree_fourierToF₂Polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree under Fourier-to-binary substitution

**Claim.** The numerical degree of the function obtained from $p$ by the Fourier-to-binary substitution equals the Fourier degree of $p$.

**Proof.** The numerical coefficient family representing the Fourier-to-binary substitution of $p$ is the Fourier-to-binary coefficient family of $p$ (`numericalCoeff_fourierToF₂Polynomial`). The numerical degree of this coefficient family equals the Fourier degree of $p$ (`numericalDegree_fourierToF₂Coeff`). Substituting these two identifications into the definition of function numerical degree proves the equality.

**Key facts.** `FABL.numericalCoeff_fourierToF₂Polynomial`, `FABL.numericalDegree_fourierToF₂Coeff`.
