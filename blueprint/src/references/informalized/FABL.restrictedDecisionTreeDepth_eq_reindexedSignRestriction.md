<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrictedDecisionTreeDepth_eq_reindexedSignRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under restricted reindexing

**Claim.** The decision-tree depth of the restricted binary function equals the depth of the corresponding reindexed restriction on the binary cube with $|J|$ coordinates.

**Proof.** First rewrite the restricted binary function as the reindexed sign restriction composed with the embedding that selects the coordinates in $J$; this is the coordinate identity supplied by `restrictedBinaryFunction_eq_comp_reindexedSignRestriction`. The decision-tree depth is unchanged when a function is viewed on a larger cube by composing with an embedding (`decisionTreeDepth_comp_embedding`). Applying that fact to the free-coordinate embedding gives the claimed equality.

**Key facts.** `FABL.restrictedBinaryFunction_eq_comp_reindexedSignRestriction`, `FABL.F₂DecisionTree.decisionTreeDepth_comp_embedding`.
