<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.productVariance_projectOnCoordinates_eq_sum_energy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a coordinate projection

**Claim.** The variance of the projection of a function onto coordinates in $S$ equals the sum of the energies of its orthogonal components indexed by nonempty subsets of $S$.

**Proof.** Use the Fourier variance identity to express the projected function's variance as a sum of squared Fourier coefficients over nonzero multi-indices. The Fourier coefficient of a coordinate projection retains the original coefficient exactly when the multi-index support is contained in the projected coordinates, and is zero otherwise (fourierCoeff_projectOnCoordinates). Thus only supports contained in $S$ contribute. By Plancherel's identity, each orthogonal component's energy is the sum of the squares of the coefficients whose support equals that component's indexing set (plancherel and fourierCoeff_orthogonalComponent). Interchanging the finite sums groups the surviving coefficients by their support. The empty support corresponds exactly to the zero multi-index (multiIndexSupport_eq_empty_iff), which is excluded by the variance formula. Every remaining support is a nonempty subset of $S$, and each coefficient is counted once, yielding the stated sum.

**Key facts.** `FABL.FiniteFourierBasis.variance_eq_sum_sq_fourierCoeff`, `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`, `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`, `FABL.FiniteFourierBasis.multiIndexSupport_eq_empty_iff`.
