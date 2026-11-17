<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.eval_recursiveMajorityThreeTreeInBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision tree evaluation on a block

**Claim.** Evaluating the tree obtained by embedding its coordinates into block $i$ gives the same output as evaluating the original tree on the restriction of $x$ to that block.

**Proof.** Reindexing a decision tree along an injective coordinate map changes each queried coordinate to its image under that map. The evaluation rule for reindexed trees (`FiniteDecisionTree.eval_reindex`) therefore says that evaluating the embedded tree on $x$ equals evaluating the original tree on the input whose coordinate $j$ is $x$ at the embedded coordinate corresponding to $j$. By definition, those coordinates are exactly the restriction of $x$ to block $i$.

**Key facts.** `FABL.FiniteDecisionTree.eval_reindex`.
