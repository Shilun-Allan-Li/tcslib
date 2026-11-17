<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.vectorFourierCoeff_setIndicator_submodule_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient on a subspace

**Claim.** If $\gamma$ belongs to the perpendicular subspace of $A$, the vector Fourier coefficient of the indicator of $A$ at $\gamma$ equals the reciprocal of the perpendicular-subspace cardinality.

**Proof.** Write the indicator of $A$ as the reciprocal of the perpendicular-subspace cardinality times the character sum over that perpendicular subspace. Insert this expression into the expectation defining the Fourier coefficient and factor out the constant. The remaining expectation is the Fourier coefficient of the character sum. Because $\gamma$ belongs to the perpendicular subspace, that coefficient is $1$, so the original coefficient is the stated reciprocal.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.setIndicator_submodule_apply`, `FABL.vectorFourierCoeff_subspaceCharacterSum_of_mem`.

**Caveat.** The supplied informal statement gives an expansion proposition rather than this membership-case coefficient formula; this account follows the formal theorem and proof source.
