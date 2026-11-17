<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.theorem71_finiteIndexedNoRegretBound_normalized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Indexed No-Regret Bound

**Claim.** For a normalized payoff and any finite indexed row sample with at least two indices, the game's upper value is at most the sample's lower value.

**Proof.** Fix $\varepsilon>0$, let $K$ be the sample's lower value, and put $c=K+\varepsilon$. The finite-column minimax step (`finiteIndexed_column_sample_step`) shows that for every finite set of columns there is a row in $X$ satisfying all the corresponding sublevel constraints at level $c$. Compactness of $X$ turns these finite intersection conditions into a single row $x_0\in X$ satisfying $f(x_0,y)\le c$ for every $y\in Y$ (`exists_forall_le_of_finite_sublevel_intersections`). Hence $\sup_y f(x_0,y)\le c$.

The normalized payoff is nonnegative, so the range of row-wise suprema is bounded below (`bddBelow_range_iSup_of_unitInterval`). The infimum over all rows is therefore at most the supremum payoff of this particular row. Consequently the upper value is at most $K+\varepsilon$. Letting $\varepsilon$ decrease to zero proves the claim.

**Key facts.** `OnlineLearning.finiteIndexed_column_sample_step`, `OnlineLearning.exists_forall_le_of_finite_sublevel_intersections`, `OnlineLearning.bddBelow_range_iSup_of_unitInterval`.
