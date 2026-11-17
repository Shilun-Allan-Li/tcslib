<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.restrictedDecisionTreeDepth_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted depth dimension bound

**Claim.** For every Boolean function and every choice of restricted coordinates and fixed signs, the restricted decision-tree depth is at most the ambient dimension $n$.

**Proof.** Choose a decision tree computing the restricted binary function whose depth attains its minimum; the existence result `exists_computingTree_depth_eq_decisionTreeDepth` provides such a tree and identifies its depth with the restricted decision-tree depth. Every decision tree on $n$ coordinates has depth at most $n$ (`depth_le_dimension`), since a path can query each available coordinate at most once. The chosen tree therefore gives the desired bound.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth`, `FABL.F₂DecisionTree.depth_le_dimension`.
