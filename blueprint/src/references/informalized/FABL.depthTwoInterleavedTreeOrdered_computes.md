<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInterleavedTreeOrdered_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the ordered interleaved tree

**Claim.** For any three distinct block positions and any choices of their seeds, the ordered interleaved decision tree computes recursive three-way majority of depth two.

**Proof.** Fix an input and evaluate the tree. Its first two queried coordinates are the selected initial coordinates in the first and second blocks. The corresponding completion trees recover the majority value of each of those blocks when supplied the first queried value as the known coordinate; the evaluation tree on the third block computes that block's majority directly. The initial-coordinate and evaluation identities, together with the fact that appending disjoint trees evaluates the second tree after the first, reduce the calculation to the finishing rule. If the first two observed signs agree, the equal-finishing rule returns the majority of the three block values. If they differ, the different-finishing rule returns that same majority using the third block value. In either case, the permutation identity for the three-way majority pair rule identifies this output with the majority of the block values in their natural order. Finally, recursive majority at depth two is the majority of the three depth-one block values, by the successor equation for recursive majority and the one-block identity. Hence the tree's evaluation equals the desired recursive majority on every input.

**Key facts.** `FABL.FiniteDecisionTree.eval_castAvailable`, `FABL.FiniteDecisionTree.eval_thenOnDisjoint`, `FABL.eval_depthTwoCompletionTree_known_initial`, `FABL.eval_depthTwoEvaluationTree`, `FABL.eval_depthTwoFinishEqual`, `FABL.eval_depthTwoFinishDifferent`, `FABL.eval_depthTwoInitialTree`, `FABL.majorityThreePairValue_permutation`, `FABL.recursiveMajority_succ`, `FABL.recursiveMajorityThree_one_block`.
