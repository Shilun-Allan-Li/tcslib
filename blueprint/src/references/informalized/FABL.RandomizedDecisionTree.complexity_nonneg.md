<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.complexity_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Randomized Complexity

**Claim.** For a finite nonempty input alphabet, the randomized decision-tree complexity of any function on length-$n$ inputs is nonnegative.

**Proof.** By definition, the complexity is the infimum of the worst-case costs of randomized trees computing the function. This family of costs is nonempty: the complete deterministic decision tree computes the function (`completeTree_computes`), and it can be viewed as a randomized tree. Every member of the family is nonnegative by the worst-case-cost bound (`worstCaseCost_nonneg`). Therefore zero is a lower bound for a nonempty family of costs, so its infimum is at least zero.

**Key facts.** `FABL.FiniteDecisionTree.completeTree_computes`, `FABL.RandomizedDecisionTree.worstCaseCost_nonneg`.
