<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.eval_recursiveNandTreeInBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision tree evaluation on a block

**Claim.** Evaluating the tree obtained by embedding its coordinates into block $i$ gives the same output as evaluating the original tree on the restriction of $x$ to that block.

**Proof.** Reindexing a decision tree along the block embedding replaces every queried coordinate by its image. The evaluation identity for reindexed trees (`FiniteDecisionTree.eval_reindex`) states that the resulting tree evaluated on $x$ agrees with the original tree evaluated on the input formed by reading $x$ at each embedded coordinate. By the definition of the block restriction, this input is precisely the restriction of $x$ to block $i$.

**Key facts.** `FABL.FiniteDecisionTree.eval_reindex`.
