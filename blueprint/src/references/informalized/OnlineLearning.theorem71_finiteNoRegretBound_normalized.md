<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxNoRegret.lean :: OnlineLearning.theorem71_finiteNoRegretBound_normalized -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Sample No-Regret Bound

**Claim.** For a normalized payoff under the convex-compact minimax hypotheses, every nonempty finite row sample has lower value at least the game's upper value.

**Proof.** Take a nonempty finite sample $u$ and split according to its cardinality. If $u$ has at least two points, reindex it by $\mathrm{Fin}(u.card)$ and apply the indexed no-regret bound (`theorem71_finiteIndexedNoRegretBound_normalized`). For each column, the infimum over the reindexed sample is at most the infimum over $u$, since the reindexing lists every point of $u$. Taking suprema over columns transfers the indexed bound to the sample $u$.

If $u$ has at most one point, nonemptiness makes it a singleton, say $\{x_0\}$. The infimum over all rows of their supremum payoffs is at most the supremum payoff of $x_0$; the required lower bound on the range of these suprema follows from normalization (`bddBelow_range_iSup_of_unitInterval`). For each column, the infimum over the singleton equals $f(x_0,y)$. Taking the supremum over columns identifies the singleton sample's lower value with the supremum payoff of $x_0$, proving the result in this case as well.

**Key facts.** `OnlineLearning.theorem71_finiteIndexedNoRegretBound_normalized`, `OnlineLearning.bddBelow_range_iSup_of_unitInterval`.
