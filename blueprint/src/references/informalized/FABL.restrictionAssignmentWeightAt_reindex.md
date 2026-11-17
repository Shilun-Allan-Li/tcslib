<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrictionAssignmentWeightAt_reindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reindexing assignment weights

**Claim.** Pulling a restriction assignment back along a bijection between finite coordinate sets preserves its product weight.

**Proof.** Expand the weight as a product over the source coordinates. Each factor is the coordinate weight of the assignment at the image of that coordinate. Because the map is a bijection, these image coordinates run through the target set exactly once; reordering the finite factors therefore gives the original product.
