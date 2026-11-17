<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkPad.lean :: Randomized.three_quarters_le_randProb_padWalk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Success probability of a padded graph walk

**Claim.** For a symmetric relation and a pair of vertices connected by a finite sequence of relation steps, the specified random padded walk visits the target with probability at least $3/4$.

**Proof.** First, the number of edge slots is $D=\operatorname{padDegree}(n)$. Since the starting vertex belongs to $\mathrm{Fin}(n)$, we have $n>0$. The padded-degree bound gives $D\le 2n$. The padded graph preserves reachability: the given finite sequence of relation steps yields a finite sequence of adjacent vertices in that graph, by the equivalence between relation reachability and padded-graph reachability ($\texttt{padGraph_reflTransGen_iff}$). The hit-probability bound for a regular multigraph says that if its degree is at most twice its number of vertices, then a walk of length $100|V|^4$ from a vertex connected to the target hits it with probability at least $3/4$ ($\texttt{RegularMultigraph.three_quarters_le_hitProb}$). Here $|V|=n$, so this applies. Finally, decoding the uniformly chosen binary word into edge slots has exactly the hit probability of that walk ($\texttt{RegularMultigraph.randProb_hits_decodeIdx}$), giving the claimed bound.

**Key facts.** `Randomized.RegularMultigraph.randProb_hits_decodeIdx`, `Randomized.padDegree_le`, `Randomized.padGraph_reflTransGen_iff`, `Randomized.RegularMultigraph.three_quarters_le_hitProb`.
