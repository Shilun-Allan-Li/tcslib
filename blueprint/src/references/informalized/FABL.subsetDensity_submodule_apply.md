<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.subsetDensity_submodule_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subspace density character sum

**Claim.** For a subspace of the Boolean cube, its probability density at any point equals the sum of the characters indexed by its perpendicular subspace, evaluated at that point.

**Proof.** First express the subset density at the point by its defining density-value function (\(`FABL.subsetDensity_apply`\)). For a subspace, its uniform probability equals the inverse cardinality of its perpendicular subspace (\(`FABL.subspaceUniformProbability_eq_inversePerpendicularCard`\)); substituting this into the density leaves the inverse of that quantity multiplying the subspace indicator. The indicator identity (\(`FABL.setIndicator_submodule_apply`\)) expresses that indicator as the inverse perpendicular cardinality times the character sum. The two scalar factors cancel, giving the stated character sum.

**Key facts.** `FABL.subsetDensity_apply`, `FABL.subspaceUniformProbability_eq_inversePerpendicularCard`, `FABL.setIndicator_submodule_apply`.
