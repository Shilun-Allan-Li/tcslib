<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.productMean_projectOnCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Preservation by Coordinate Projection

**Claim.** Projecting a function onto any subset of the coordinates preserves its product mean.

**Proof.** Represent the product mean as the Fourier coefficient at the all-constant multi-index (`fourierCoeff_zeroMultiIndex`). The coefficient formula for projection onto $J$ (`fourierCoeff_projectOnCoordinates`) says that a coefficient is retained precisely when the support of its multi-index is contained in $J$. The all-constant multi-index has empty support, and the empty set is contained in every $J$, so this coefficient is retained unchanged. Converting that coefficient back to the product mean proves the equality.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_zeroMultiIndex`, `FABL.FiniteFourierBasis.fourierCoeff_projectOnCoordinates`.
