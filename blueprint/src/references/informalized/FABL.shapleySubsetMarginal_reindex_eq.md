<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.shapleySubsetMarginal_reindex_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reindexed Shapley Marginal

**Claim.** The restriction to $J$ of a Shapley-random subset, reindexed by the enumeration of $J$, has the Shapley subset distribution on $|J|$ elements.

**Proof.** First identify the marginal distribution with the Shapley subset distribution on subsets of $J$ (the marginal-to-restricted-distribution identity, `shapleySubsetMarginalPMF_eq_shapleySubsetPMFOn`). Both sides of the desired equality are then images under finite equivalences. For a probability mass function mapped along an equivalence, its mass at a point is the original mass at the inverse image of that point (`pmf_map_equiv_apply`). Applying this formula to both images reduces the claim to equality of the corresponding inverse-image subsets. An element belongs to one of these subsets exactly when its reindexed element belongs to the other, so the subsets agree; hence their masses agree at every point.

**Key facts.** `FABL.shapleySubsetMarginalPMF_eq_shapleySubsetPMFOn`, `FABL.pmf_map_equiv_apply`.
