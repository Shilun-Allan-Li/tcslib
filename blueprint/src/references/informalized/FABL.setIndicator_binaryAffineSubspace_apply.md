<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.setIndicator_binaryAffineSubspace_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Subspace Indicator Formula

**Claim.** The indicator of the affine subspace $a+H$ at $x$ is the reciprocal of $2^{\operatorname{codim}(H)}$ times the sum of the characters indexed by vectors perpendicular to $H$, evaluated at $x+a$.

**Proof.** The affine-subspace indicator at $x$ equals the indicator of $H$ at $x+a$ (`setIndicator_binaryAffineSubspace_eq_translate`). Apply the subspace indicator formula to $H$ at $x+a$ (`setIndicator_submodule_apply`): it is the reciprocal of $2^{\operatorname{codim}(H)}$ multiplied by the sum of the characters indexed by vectors perpendicular to $H$, evaluated at $x+a$. This is the asserted identity.

**Key facts.** `FABL.setIndicator_binaryAffineSubspace_eq_translate`, `FABL.setIndicator_submodule_apply`.
