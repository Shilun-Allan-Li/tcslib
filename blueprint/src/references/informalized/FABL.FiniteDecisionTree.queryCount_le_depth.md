<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.queryCount_le_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count bounded by tree depth

**Claim.** On any input, the number of queries made by a finite decision tree is at most its depth, the maximum number of queries along any branch.

**Proof.** Induct on the tree. A leaf makes zero queries and has depth zero. At a query node, the trace consists of the root query followed by the trace of the child selected by the input value at that coordinate. By induction, the child’s query count is at most its depth. That child depth is at most the maximum depth among all children, which is the supremum used to define the root depth. Adding one to both sides yields the required bound.
