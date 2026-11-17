<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.card_perpendicularSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the Perpendicular Subspace

**Claim.** If $d$ is the dimension of the perpendicular subspace $A^\perp$ over the field with two elements, then $A^\perp$ has cardinality $2^d$.

**Proof.** Apply the finite-subspace cardinality formula, which states that a subspace over the two-element field with dimension $d$ has $2^d$ elements (`FABL.card_submodule_eq_two_pow_finrank`). Taking the subspace to be $A^\perp$, its dimension is precisely the stated $d$.

**Key facts.** `FABL.card_submodule_eq_two_pow_finrank`.
