<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.averageDecisionTreeComplexity_majority_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Three Average Complexity

**Claim.** For uniform input to majority on three signs, the minimum expected query cost of a randomized decision tree is $5/2$.

**Proof.** The lower bound theorem `averageDecisionTreeComplexity_majority_three_le` gives that the infimum of the average costs is at most $5/2$. For the reverse inequality, use the definition of average complexity as the infimum of the costs of all correct randomized trees. The deterministic tree that queries coordinates in order and stops as soon as the observed signs determine the majority provides a nonempty family of such costs. Every tree in that family has average cost at least $5/2$, by the bound `majorityThree_averageCost_ge`; hence their infimum is at least $5/2$. The two inequalities give equality.

**Key facts.** `FABL.averageDecisionTreeComplexity_majority_three_le`, `FABL.RandomizedDecisionTree.majorityThree_averageCost_ge`.
