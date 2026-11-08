<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.randomizedDecisionTreeComplexity_recursiveMajority_three_two_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Depth-Two Majority Bound

**Claim.** The randomized decision-tree complexity of depth-two recursive majority on $3^2$ signs is strictly less than $(8/3)^2$.

**Proof.** The complexity is at most $571/81$ (\texttt{randomizedDecisionTreeComplexity\_recursiveMajority\_three\_two\_le}). The numerical comparison $571/81<(8/3)^2$, with the latter expressed as the depth-two recursive majority cost bound, is given by \texttt{five\_seventy\_one\_div\_eighty\_one\_lt\_recursiveMajorityRandomizedCostBound\_two}. Combining these inequalities gives the strict bound.

**Key facts.** `FABL.randomizedDecisionTreeComplexity_recursiveMajority_three_two_le`, `FABL.five_seventy_one_div_eighty_one_lt_recursiveMajorityRandomizedCostBound_two`.
