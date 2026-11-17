<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.decisionTreeDepth_le_canonicalBlockTree_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Bound from the Canonical Tree

**Claim.** The decision-tree depth of the function obtained by restricting a DNF formula is at most the depth of its canonical block tree.

**Proof.** The canonical block tree computes the restricted function, by the computation theorem for that tree (`FABL.DNFFormula.canonicalBlockTree_computes`). A decision-tree depth is no greater than the depth of any decision tree computing the same function (`FABL.F₂DecisionTree.decisionTreeDepth_le_of_computes`). Applying this bound to the canonical block tree gives the result.

**Key facts.** `FABL.DNFFormula.canonicalBlockTree_computes`, `FABL.F₂DecisionTree.decisionTreeDepth_le_of_computes`.
