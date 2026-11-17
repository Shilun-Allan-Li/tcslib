<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: prefixGameLoss_eq_cumLoss -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Loss Identity

**Claim.** The cumulative loss of row action $i$ over the first $t$ column actions equals its cumulative loss in the induced loss sequence through round $t$.

**Proof.** The prefix sum ranges over indices $s\in\mathrm{Fin}\,t.val$. Map each such index to the index with the same value in $\mathrm{Fin}\,T$; since $t<T$, its value is less than $t.val$. This map is a bijection onto the indices in $\mathrm{Fin}\,T$ whose values are less than $t.val$: every such index comes from its own value in $\mathrm{Fin}\,t.val$, and equal image indices have equal values. Under this correspondence, the summand is unchanged, since the induced loss at the mapped index is $1-G.payoff(i,actions(s))$. Therefore the two finite sums agree.
