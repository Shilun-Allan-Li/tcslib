<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.vectorFourierCoeff_setIndicator_binaryAffineSubspace_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient on an affine subspace

**Claim.** If $\gamma$ belongs to the perpendicular subspace of $H$, the vector Fourier coefficient of the indicator of the affine translate $H+a$ at $\gamma$ equals the Walsh character indexed by $\gamma$ evaluated at $a$, multiplied by the reciprocal of the perpendicular-subspace cardinality.

**Proof.** Express the indicator of $H+a$ as the indicator of $H$ evaluated at $x+a$. The translation rule for Fourier coefficients then says its coefficient is the character at $a$ times the coefficient of the indicator of $H$. Since $\gamma$ belongs to the perpendicular subspace of $H$, that latter coefficient is the reciprocal of the perpendicular-subspace cardinality. Combining these gives the formula.

**Key facts.** `FABL.setIndicator_binaryAffineSubspace_eq_translate`, `FABL.vectorFourierCoeff_translate_add`, `FABL.vectorFourierCoeff_setIndicator_submodule_of_mem`.

**Caveat.** The supplied informal statement includes additional affine-subspace conclusions; this account follows the narrower formal theorem.
