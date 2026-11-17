<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.averageComplexity_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Average Complexity

**Claim.** For a finite input alphabet with distribution $\pi$, the infimum of the average query costs of finite randomized decision trees computing $f$ is nonnegative.

**Proof.** By definition, the average complexity is the infimum of the set of average costs realized by such trees. This set is nonempty: the distribution has nonempty support, so the alphabet is nonempty, and the complete decision tree for $f$ is therefore available. The complete-tree correctness result (`FiniteDecisionTree.completeTree_computes`) ensures that this tree computes $f$; viewing it as a randomized tree with a deterministic seed gives an average cost in the set. Every member of the set is nonnegative, by the nonnegativity of average cost (`RandomizedDecisionTree.averageCost_nonneg`). Thus zero is a lower bound for a nonempty set of costs, and its infimum is at least zero.

**Key facts.** `FABL.FiniteDecisionTree.completeTree_computes`, `FABL.RandomizedDecisionTree.averageCost_nonneg`.
