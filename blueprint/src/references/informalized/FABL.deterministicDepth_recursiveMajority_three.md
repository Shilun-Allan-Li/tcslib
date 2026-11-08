<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.deterministicDepth_recursiveMajority_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Majority Decision-Tree Depth

**Claim.** For recursive majority on $3^d$ inputs, the minimum deterministic decision-tree depth is $3^d$.

**Proof.** Choose a tree computing recursive majority whose depth equals the minimum depth; such a tree exists by `exists_computingTree_depth_eq_deterministicDepth`. Its depth is at most the number of available input coordinates, by the general depth bound `depth_le_dimension`, giving the upper bound $3^d$. Conversely, every tree computing recursive majority has depth at least $3^d$, by `recursiveMajorityThree_depth_le`. Applying this to the chosen minimum-depth tree gives the matching lower bound, hence equality.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_depth_eq_deterministicDepth`, `FABL.FiniteDecisionTree.depth_le_dimension`, `FABL.FiniteDecisionTree.recursiveMajorityThree_depth_le`.
