<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Exchange.lean :: Kruskal.uf_exchange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Union-find exchange

**Claim.** When the endpoints of $e$ are separate in the initial union-find state but connected after merging the edges of $S$, some edge $f$ of $S$ can be removed after first merging the endpoints of $e$, without changing the final partition.

**Proof.** The initial state represents exactly the reachability classes of $\mathit{base}$. By the characterization of merging as adding reachability edges (\texttt{Kruskal.mergeAll_iff_reach}), the hypothesis that the endpoints of $e$ become joined after merging $S$ says they are connected in $\mathit{base} ++ S$. They are not connected in $\mathit{base}$, since such a connection would contradict their initial separation. Also, the endpoints are distinct: equal endpoints would already have equal representatives. The exchange lemma for reachability therefore gives an edge $f\in S$ such that every connection in $\mathit{base} ++ S$ remains a connection in $\mathit{base} ++ S.erase\ f ++ [e]$ (\texttt{Kruskal.exchange_with_base}). The reverse inclusion of reachability is proved by lifting each edge of the latter list back to the former: base edges remain, edges in $S.erase\ f$ occur in $S$, and the added edge $e$ is itself connected in $\mathit{base} ++ S$ by the original merged-state hypothesis. Reachability is symmetric, so either orientation of that last edge is covered. Thus the two lists have exactly the same reachability relation, using reachability lifting (\texttt{Kruskal.reach_lift}) and monotonicity (\texttt{Kruskal.reach_mono}) for the unchanged edges. Finally, apply the merge-to-reachability characterization to both merge sequences. Their representative-equality relations coincide, which is precisely equality of the induced partitions.

**Key facts.** `Kruskal.exchange_with_base`, `Kruskal.mergeAll_iff_reach`, `Kruskal.reach_lift`, `Kruskal.reach_mono`.
