<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.projectOnCoordinates_projectOnCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Coordinate Projections

**Claim.** Successive projections onto $J$ and then $I$ equal the projection onto $I\cap J$.

**Proof.** By injectivity of the Fourier coefficient map (\texttt{FABL.FiniteFourierBasis.fourierCoeff_injective}), it is enough to compare coefficients at each multi-index. The coefficient formula for a projection (\texttt{FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates}) reduces the comparison to whether the multi-index support is contained in $I$, in $J$, and in $I\cap J$. If the support is contained in both $I$ and $J$, it is contained in their intersection, so both successive projections retain the coefficient. If it is contained in $I$ but not $J$, the second projection removes it, and the support is not contained in the intersection either. If it is not contained in $I$, the first projection already removes it, and the support again cannot be contained in the intersection. In each case the coefficients on the two sides agree. Injectivity now yields the function equality.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_injective`, `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`.
