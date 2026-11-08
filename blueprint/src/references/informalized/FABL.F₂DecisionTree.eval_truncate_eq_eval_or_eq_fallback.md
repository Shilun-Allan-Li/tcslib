<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.eval_truncate_eq_eval_or_eq_fallback -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Truncated Tree

**Claim.** The evaluation of a tree truncated at depth $k$ is either the original tree’s evaluation or the fallback value.

**Proof.** Induct on the tree. A leaf remains unchanged by truncation, so its truncated evaluation equals its original evaluation. At a query node with $k=0$, truncation replaces the node by a leaf labeled with the fallback, so the truncated evaluation is the fallback. For $k+1$, the input selects the zero child if the queried coordinate is $0$, and the one child otherwise. Apply the induction hypothesis to the selected child with truncation depth $k$; its truncated evaluation is either that child’s original evaluation or the fallback. Because both the original and truncated trees follow the same branch at the root, these alternatives give the claimed result for the whole tree.
