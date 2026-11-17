<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.depth_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bounded by dimension

**Claim.** A decision tree on all $n$ coordinates has depth at most $n$.

**Proof.** The depth bound by the number of available coordinates (`FABL.F₂DecisionTree.depth_le_card_available`) gives depth at most the cardinality of the available set. For a tree on all coordinates, that set is the full set of $n$ coordinates, whose cardinality is $n$.

**Key facts.** `FABL.F₂DecisionTree.depth_le_card_available`.
