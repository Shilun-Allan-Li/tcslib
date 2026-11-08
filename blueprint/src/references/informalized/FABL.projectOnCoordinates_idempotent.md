<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.projectOnCoordinates_idempotent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idempotence of Coordinate Projection

**Claim.** Applying the coordinate projection onto $J$ twice gives the same function as applying it once.

**Proof.** Use injectivity of the Fourier coefficient map (\texttt{FABL.FiniteFourierBasis.fourierCoeff_injective}), so it suffices to compare the coefficients of the two projected functions at each multi-index. The projection coefficient formula (\texttt{FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates}) says that projection retains a coefficient exactly when the multi-index support is contained in $J$, and otherwise sets it to zero. If the support is contained in $J$, both projections retain the original coefficient; if it is not, both sides have coefficient zero. Thus all coefficients agree, and injectivity gives the claimed equality.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`.
