<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.averageComplexity_zero_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Complexity in Dimension Zero

**Claim.** When there are no input coordinates, the minimum average query complexity of a finite randomized decision tree computing $g$ is zero.

**Proof.** Since the input distribution has nonempty support, the alphabet is nonempty. Take the complete decision tree for $g$ and view it as a deterministic randomized tree. The complete-tree correctness result (`FiniteDecisionTree.completeTree_computes`) confirms that it computes $g$. In dimension zero, every such tree has average cost zero (`RandomizedDecisionTree.averageCost_zero_dimension`), so the infimum of achievable costs is at most zero by the bound on complexity by the cost of any particular tree (`RandomizedDecisionTree.averageComplexity_le_averageCost`). The general nonnegativity of average complexity (`RandomizedDecisionTree.averageComplexity_nonneg`) gives the reverse inequality. Hence the complexity equals zero.

**Key facts.** `FABL.FiniteDecisionTree.completeTree_computes`, `FABL.RandomizedDecisionTree.averageComplexity_le_averageCost`, `FABL.RandomizedDecisionTree.averageCost_zero_dimension`, `FABL.RandomizedDecisionTree.averageComplexity_nonneg`.
