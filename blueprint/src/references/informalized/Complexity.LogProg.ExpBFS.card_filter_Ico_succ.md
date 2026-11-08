<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean :: Complexity.LogProg.ExpBFS.card_filter_Ico_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Filtered Interval Cardinality Recurrence

**Claim.** For a decidable predicate $p$ and $u<K$, the number of elements of $[u,K)$ satisfying $p$ is the indicator of $p(u)$ plus the number satisfying $p$ in $[u+1,K)$.

**Proof.** Express each filtered cardinality as a sum of the predicate’s indicator over the corresponding interval. The interval-sum recurrence \texttt{Finset.sum_eq_sum_Ico_succ_bot} separates the first term, at $u$, from the sum over $[u+1,K)$. That first term is $1$ when $p(u)$ holds and $0$ otherwise, yielding the formula.
