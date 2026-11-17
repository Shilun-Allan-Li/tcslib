<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.cover_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability in the Two-Sheeted Lift

**Claim.** For a connected regular multigraph that is not bipartite, every pair of vertices can be joined in the two-sheeted lift from the false copy of the first vertex to the false copy of the second.

**Proof.** Let $S(x)$ mean that $(u,\mathrm{false})$ reaches $x$ in the lifted graph. Connectivity and the path-lifting property ($\texttt{cover\_lift}$) show that for every vertex $w$, at least one of $(w,\mathrm{false})$ and $(w,\mathrm{true})$ lies in $S$. If both copies of some $w$ lie in $S$, lift a base path from $w$ to $v$. Its lifted endpoint flips the Boolean label according to the path, so choose the starting copy matching that flip; concatenating the two lifted paths reaches $(v,\mathrm{false})$. If no vertex has both copies in $S$, define a coloring by assigning $w$ the Boolean value indicating whether its true copy lies in $S$. The preceding existence of at least one reachable copy and the assumption that both are never reachable ensure that this coloring records exactly which copy is reachable. A lifted edge flips the label and preserves reachability from the starting point, so the neighbor of $w$ has the opposite color. This would make the graph bipartite, contrary to hypothesis. Thus some vertex has both copies reachable, and the desired lifted reachability follows.

**Key facts.** `Randomized.RegularMultigraph.cover_lift`.
