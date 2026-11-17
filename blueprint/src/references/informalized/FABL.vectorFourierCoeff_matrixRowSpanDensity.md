<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.vectorFourierCoeff_matrixRowSpanDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of a row-span density

**Claim.** For a matrix $H$, the vector Fourier coefficient of its row-span density at $\gamma$ is $1$ if $H\gamma=0$ and $0$ otherwise.

**Proof.** First identify the row-span density with the character sum over the perpendicular subspace of the row span. Split into the two cases. If $H\gamma=0$, the criterion for membership in that perpendicular subspace shows that $\gamma$ belongs to it, and the Fourier coefficient of its character sum is $1$. If $H\gamma\ne0$, the same criterion shows that $\gamma$ is outside the perpendicular subspace, and the coefficient is $0}.

**Key facts.** `FABL.subsetDensity_submodule_fourier_expansion`, `FABL.mem_perpendicular_matrixRowSpan_iff_mulVec_eq_zero`, `FABL.vectorFourierCoeff_subspaceCharacterSum_of_mem`, `FABL.vectorFourierCoeff_subspaceCharacterSum_of_not_mem`.

**Caveat.** The supplied informal statement describes a different expansion; this account follows the formal theorem and proof source.
