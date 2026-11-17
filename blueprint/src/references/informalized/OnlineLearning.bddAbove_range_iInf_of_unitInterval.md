<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.bddAbove_range_iInf_of_unitInterval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Infima of Bounded Families

**Claim.** For nonempty $\iota$, if every $g(i,j)$ lies between $0$ and $1$, then the function assigning to $j$ the infimum of $g(i,j)$ over $i$ has range bounded above.

**Proof.** Use $1$ as an upper bound for the range. Fix any $j$. Since all values $g(i,j)$ are nonnegative, their range as $i$ varies is bounded below, so its infimum exists. The infimum is at most any member of the family; in particular, it is at most $g(i_0,j)$ for a chosen index $i_0\in\iota$. The unit-interval hypothesis gives $g(i_0,j)\le1$. Hence the infimum is at most $1$ for every $j$, as required.

**Key facts.** `OnlineLearning.bddBelow_of_nonneg`.
