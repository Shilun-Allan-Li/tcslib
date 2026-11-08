<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.productInner_eq_project_inter_of_dependsOnly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Product After Coordinate Projection

**Claim.** If $f$ depends only on coordinates in $I$ and $g$ only on coordinates in $J$, then their product inner product equals the inner product of their projections onto the shared coordinates $I\cap J$.

**Proof.** Apply the product-space Plancherel identity to both inner products, writing each as a sum over multi-indices of products of Fourier coefficients (`FiniteFourierBasis.plancherel`). For each index, projection onto a coordinate set preserves its Fourier coefficient precisely when the index support is contained in that set, and otherwise makes the coefficient zero (`FiniteFourierBasis.fourierCoeff_projectOnCoordinates`). If the support lies in both $I$ and $J$, it lies in $I\cap J$, so the summand is unchanged. If it fails containment in either set, the function depending only on that set has zero coefficient there (`FiniteFourierBasis.fourierCoeff_eq_zero_of_dependsOnly`); the projected inner-product summand also vanishes because the support cannot lie in the intersection. Thus the summands agree for every multi-index, and so do the inner products.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`, `FABL.FiniteFourierBasis.fourierCoeff_eq_zero_of_dependsOnly`.
