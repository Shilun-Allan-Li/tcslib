<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.randomizedDecisionTreeComplexity_recursiveMajority_three_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-Two Recursive Majority Bound

**Claim.** The randomized decision-tree complexity of depth-two recursive majority on $3^2$ signs is at most $571/81$.

**Proof.** The depth-two interleaved randomized tree is a zero-error tree for this recursive majority function. Since every worst-case cost is nonnegative, the set of costs over which the complexity takes its infimum is bounded below by zero. The infimum is therefore no greater than the cost of this exhibited tree. Its worst-case cost is at most $571/81$ (\texttt{depthTwoInterleavedRandomizedTree\_worstCaseCost\_le}), proving the bound.

**Key facts.** `FABL.RandomizedDecisionTree.worstCaseCost_nonneg`, `FABL.depthTwoInterleavedRandomizedTree_worstCaseCost_le`.
