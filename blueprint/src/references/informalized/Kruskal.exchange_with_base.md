<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Exchange.lean :: Kruskal.exchange_with_base -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Base-Relative Edge Exchange

**Claim.** If the endpoints of an edge are connected using the base edges and a list $S$, but not using the base alone, then some edge of $S$ can be removed and the given edge appended while preserving every connection made by the original combined list.

**Proof.** Proceed by induction on $S$, generalizing the base list. If $S$ is empty, the assumed connection would already be a connection through the base, contrary to the hypothesis, so this case is impossible. For the inductive step, write $S=g::S'$. First ask whether the endpoints of $e$ are already connected through $\mathit{base}++S'$. If they are, apply the induction hypothesis to $S'$ to obtain an edge $f$ whose removal and replacement by $e$ preserves reachability for $\mathit{base}++S'$. The edge $g$ is retained. A path using $\mathit{base}++(g::S')$ either avoids $g$, in which case the induction conclusion applies directly, or uses $g$. In the latter case, split the path at the endpoints of $g$: the two resulting portions are preserved by the induction conclusion, and the edge $g$ itself is still present, so they concatenate to a path in the new list.

Otherwise, the endpoints of $e$ are not connected through $\mathit{base}++S'$. The reachability decomposition for adjoining one edge (Kruskal.reach_cons_iff), together with invariance of reachability under replacing a list by one with the same edge-membership (Kruskal.reach_mem_iff), shows that their original connection must use $g$ to cross between its endpoints. There are two possible orientations: either $e.u$ reaches $g.u$ and $g.v$ reaches $e.v$, or $e.u$ reaches $g.v$ and $g.u$ reaches $e.v$, all through $\mathit{base}++S'$. In the first case, the head-edge exchange result (Kruskal.exchange_take_head) shows that every connection through $\mathit{base}++(g::S')$ remains after replacing $g$ by $e$ at the end. In the second case, its reversed-orientation version (Kruskal.exchange_take_head') gives the same conclusion. Thus choose $f=g$, which belongs to $S$; the resulting list is exactly $\mathit{base}++S.erase\ f++[e]$, and all original connections persist.

**Key facts.** `Kruskal.reach_cons_iff`, `Kruskal.reach_mem_iff`, `Kruskal.exchange_take_head`, `Kruskal.exchange_take_head'`.

**Caveat.** The first induction branch in the supplied proof contains detailed list-membership case splits; the account summarizes these as preserving paths through the retained head edge. The explicit distinct-endpoints hypothesis does not appear to be needed in the described argument.
