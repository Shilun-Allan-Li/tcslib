<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrictedDecisionTreeDepth_reindexBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under coordinate reindexing

**Claim.** Reindexing the coordinates of a Boolean function by a bijection, while transporting the free and fixed-coordinate statuses along that bijection, preserves the decision-tree depth of its restriction.

**Proof.** The restriction of the reindexed function is the original restricted function composed with the coordinate bijection (`CoordRestriction.restrict_reindexBooleanFunction`). Decision-tree depth is invariant under composition with a bijection of coordinates (`decisionTreeDepth_comp_equiv`). Applying this invariance to the restriction proves the equality.

**Key facts.** `FABL.CoordRestriction.restrict_reindexBooleanFunction`, `FABL.F₂DecisionTree.decisionTreeDepth_comp_equiv`.
