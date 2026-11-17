<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.spectralInfinityNorm_setIndicator_binaryAffineSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine-subspace indicator spectral norm

**Claim.** For a linear subspace $H$ and a translate $H+a$ over $\mathbb F_2^n$, the spectral infinity norm of its indicator is the reciprocal of the size of the perpendicular subspace, expressed as $2^{-\operatorname{codim}(H)}$ under the given codimension convention.

**Proof.** For any frequency $\gamma$, if $\gamma$ lies in the perpendicular subspace of $H$, the absolute value of the Fourier coefficient of the affine-subspace indicator is the reciprocal perpendicular-cardinality (`FABL.abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem`). Otherwise that absolute value is zero (`FABL.abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem`). Since the reciprocal perpendicular-cardinality is positive (`FABL.inversePerpendicularCard_pos`), these cases show that every absolute coefficient is at most this value, so their supremum is at most it. For the reverse inequality, take the zero frequency, which belongs to the perpendicular subspace; its absolute coefficient equals the reciprocal perpendicular-cardinality. The supremum is therefore at least that value, proving equality.

**Key facts.** `FABL.abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem`, `FABL.abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_not_mem`, `FABL.inversePerpendicularCard_pos`.

**Caveat.** The formal theorem establishes the spectral infinity norm identity only; the additional Fourier expansion, sparsity, granularity, and $L^1$ claims in the informal statement are not proved here.
