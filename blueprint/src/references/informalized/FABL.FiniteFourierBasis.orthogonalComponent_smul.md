<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalComponent_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar linearity of components

**Claim.** Multiplying a function by a scalar multiplies each of its orthogonal components by the same scalar.

**Proof.** Use injectivity of the Fourier coefficient map to compare the two functions ($\texttt{FABL.FiniteFourierBasis.fourierCoeff_injective}$). At each multi-index, the coefficient of an orthogonal component is the original coefficient if the index has the specified support and is zero otherwise ($\texttt{FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent}$). Fourier coefficients also scale by the scalar ($\texttt{FABL.FiniteFourierBasis.fourierCoeff_smul}$). In the matching-support case these identities give the same scalar multiple of the original coefficient on both sides; in the other case both coefficients are zero. Injectivity now gives equality of the functions.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`, `FABL.FiniteFourierBasis.fourierCoeff_smul`.
