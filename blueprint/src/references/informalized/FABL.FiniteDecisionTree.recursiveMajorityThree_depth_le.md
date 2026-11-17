<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.FiniteDecisionTree.recursiveMajorityThree_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Lower Bound for Recursive Majority

**Claim.** Every finite decision tree computing recursive majority on $3^d$ inputs has depth at least $3^d$.

**Proof.** Convert the given sign-valued decision tree into its real-valued version. The conversion preserves the computed Boolean function (`FiniteDecisionTree.toF₂Real_computes`), so the general degree lower bound for decision trees applies: the Fourier degree of the real-valued target is at most the depth of this converted tree (`fourierDegree_toReal_le_depth_of_decisionTree`). Recursive majority on three inputs has Fourier degree $3^d$ (`fourierDegree_recursiveMajority_three`). Thus $3^d$ is at most the converted tree’s depth. The conversion’s depth is at most the original tree’s depth (`FiniteDecisionTree.depth_toF₂Real_le`), yielding the asserted lower bound.

**Key facts.** `FABL.FiniteDecisionTree.toF₂Real_computes`, `FABL.fourierDegree_toReal_le_depth_of_decisionTree`, `FABL.fourierDegree_recursiveMajority_three`, `FABL.FiniteDecisionTree.depth_toF₂Real_le`.
