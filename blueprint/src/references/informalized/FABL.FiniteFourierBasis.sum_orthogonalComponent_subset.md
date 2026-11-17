<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.sum_orthogonalComponent_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Projection by Orthogonal Components

**Claim.** For every function on the finite product space and every coordinate set $T$, the sum of its orthogonal components indexed by subsets of $T$ equals its projection onto the coordinates in $T$.

**Proof.** Fourier coefficients determine a function uniquely, so it suffices to compare the two sides at each multi-index $a$. The coefficient of the coordinate projection is the coefficient of the original function when the support of $a$ is contained in $T$, and is zero otherwise (the Fourier coefficient formula for coordinate projection, `fourierCoeff_projectOnCoordinates`). By linearity of Fourier coefficients over finite sums (`fourierCoeff_finset_sum`) and the coefficient formula for an orthogonal component (`fourierCoeff_orthogonalComponent`), the coefficient of the proposed sum is obtained by summing over all $S\subseteq T$: only the component with $S$ equal to the support of $a$ can contribute. If that support lies in $T$, this one term contributes the original coefficient; if it does not, no term contributes. Thus the coefficients agree in every case, and injectivity of the Fourier coefficient map (`fourierCoeff_injective`) gives the desired equality.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`, `FABL.FiniteFourierBasis.fourierCoeff_finset_sum`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`, `FABL.FiniteFourierBasis.fourierCoeff_injective`.
