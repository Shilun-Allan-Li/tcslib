<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.queryCount_recursiveNandTree_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count of the recursive NAND tree

**Claim.** The recursive NAND tree first incurs the query count of the tree on the chosen initial block, then incurs zero additional queries if that block's recursive NAND value is $1$, and otherwise incurs the other block's query count; the order selects which block is first.

**Proof.** Split on whether the order coordinate is $0$. In that case the construction uses the ordered NAND tree with the left block first. Its query count is the first tree's count, plus the second tree's count exactly when the first tree evaluates to something other than $1$ (`queryCount_orderedNandTree`). The block reindexing identity converts these two counts to the counts of the depth-$d$ trees on their respective restricted inputs (`queryCount_recursiveNandTreeInBlock`). The evaluation of the first block tree is its original tree's evaluation on that restriction (`eval_recursiveNandTreeInBlock`), and the seed tree computes the recursive NAND function (`recursiveNandTree_computes`), so this is precisely the condition in the claimed formula. If the order is not $0$, the construction swaps the two blocks: the right tree is queried first, and the left tree is queried only if the right tree's value is not $1$. The same count and evaluation identities yield the second formula. Casting a tree to an equal available-coordinate set preserves its query count (`FiniteDecisionTree.queryCount_castAvailable`).

**Key facts.** `FABL.FiniteDecisionTree.queryCount_castAvailable`, `FABL.queryCount_orderedNandTree`, `FABL.queryCount_recursiveNandTreeInBlock`, `FABL.eval_recursiveNandTreeInBlock`, `FABL.recursiveNandTree_computes`.
