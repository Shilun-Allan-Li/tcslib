<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_recursiveMajorityThreeTree_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count of the recursive majority tree

**Claim.** The recursive majority tree's query count is the sum of the counts for its first two evaluated blocks, together with the third block's count precisely when the first two recursive majority values disagree; the order determines which blocks are queried first and which is the conditional continuation.

**Proof.** Split according to the order coordinate. When it is $0$, the construction uses the ordered tree on blocks $0,1,2$. Its query count is the first tree's count plus the second's, and the third's count is included exactly when the first two outputs differ (`queryCount_orderedMajorityThreeTree`). Reindexing identifies each block tree's count on the full input with its original count on the corresponding restricted block (`queryCount_recursiveMajorityThreeTreeInBlock`). The block tree's output is likewise the original tree's output on that restriction (`eval_recursiveMajorityThreeTreeInBlock`); since each depth-$d$ seed tree computes the recursive majority function (`recursiveMajorityThreeTree_computes`), these outputs are the recursive majority values appearing in the statement. When the order coordinate is $1$, the construction queries blocks $0$ and $2$ first, leaving block $1$ as the continuation, and the same count and evaluation facts give the second formula. In the remaining case, the order is $2$; the construction queries blocks $1$ and $2$ first and leaves block $0$ as the continuation, giving the final formula by the same reasoning. Changes to the available-coordinate set do not affect query counts (`FiniteDecisionTree.queryCount_castAvailable`).

**Key facts.** `FABL.FiniteDecisionTree.queryCount_castAvailable`, `FABL.queryCount_orderedMajorityThreeTree`, `FABL.queryCount_recursiveMajorityThreeTreeInBlock`, `FABL.eval_recursiveMajorityThreeTreeInBlock`, `FABL.recursiveMajorityThreeTree_computes`.
