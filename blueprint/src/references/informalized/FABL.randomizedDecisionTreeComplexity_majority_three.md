<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.randomizedDecisionTreeComplexity_majority_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority of Three Complexity

**Claim.** The randomized decision-tree complexity of $\mathrm{Maj}_3$ is $8/3$.

**Proof.** The proof establishes both inequalities. An explicit randomized decision tree, which first queries two distinct coordinates, has worst-case expected cost at most $8/3$; hence the complexity is at most $8/3$ (\texttt{randomizedDecisionTreeComplexity\_majority\_three\_le}). Conversely, every zero-error randomized decision tree computing $\mathrm{Maj}_3$ has worst-case cost at least $8/3$ (\texttt{RandomizedDecisionTree.majorityThree\_worstCaseCost\_ge}). Since every cost in the set defining the infimum is therefore at least $8/3$, its infimum is at least $8/3$. The two bounds give equality.

**Key facts.** `FABL.randomizedDecisionTreeComplexity_majority_three_le`, `FABL.RandomizedDecisionTree.majorityThree_worstCaseCost_ge`.
