<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Seeded Trees

**Claim.** For every depth $d$ and every seed at that depth, the deterministic decision tree selected by the seed computes recursive majority on inputs of length $3^d$.

**Proof.** Proceed by induction on $d$. At depth zero, the tree is the identity query on the sole input coordinate, so its evaluation is exactly the depth-zero recursive majority. For the successor step, write the seed as an order choice together with three seeds for the depth-$d$ subtrees. By induction, each subtree computes recursive majority on its corresponding input block. The ordered tree evaluates the three block trees and combines their outputs by the majority-of-three rule (`eval_orderedMajorityThreeTree`); reindexing each tree into its block makes its evaluation the depth-$d$ result on that block (`eval_recursiveMajorityThreeTreeInBlock`). If the order choice is $0$, the outputs occur in their natural order, and the pair-value rule is ordinary three-input majority (`majorityThreePairValue_eq_majority`). If the choice is $1$, the second and third outputs are exchanged; if it is neither $0$ nor $1$, the outputs are cyclically rotated. In these two cases, the corresponding symmetry identities for the pair-value rule (`majorityThreePairValue_swap_second_third` and `majorityThreePairValue_rotate`) show that the result is still majority of the same three block values. The successor equation for recursive majority (`recursiveMajority_succ`) identifies that result with recursive majority on the full input. The tree's available-coordinate set is only changed by equality casts, which do not alter evaluation (`FiniteDecisionTree.eval_castAvailable`).

**Key facts.** `FABL.FiniteDecisionTree.eval_castAvailable`, `FABL.eval_orderedMajorityThreeTree`, `FABL.eval_recursiveMajorityThreeTreeInBlock`, `FABL.majorityThreePairValue_eq_majority`, `FABL.majorityThreePairValue_swap_second_third`, `FABL.majorityThreePairValue_rotate`, `FABL.recursiveMajority_succ`.
