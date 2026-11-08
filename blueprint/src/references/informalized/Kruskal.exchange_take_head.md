<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Exchange.lean :: Kruskal.exchange_take_head -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head-Edge Exchange Preserves Reachability

**Claim.** Under the stated connections between the endpoints of the two edges, every pair connected through the list with the head edge remains connected after replacing that head edge by the appended edge.

**Proof.** First, every path using only the edges in $\mathit{base} ++ \mathit{rest}$ remains available after appending $e$, since the latter list contains all those edges. Also, $e$ itself connects its two endpoints in the new list. Now consider a path in $\mathit{base} ++ (g :: \mathit{rest})$. Each step uses an edge from that list. If the edge is not $g$, the same adjacency is present in the new list, so that step remains available. If the step uses $g$ in the direction from $g.u$ to $g.v$, replace it by a route from $g.u$ to $e.v$ using the second assumed connection, then traverse $e$ in reverse from $e.v$ to $e.u$, then use the reverse of the first assumed connection from $e.u$ to $g.u$—more directly, the required route from $g.u$ to $g.v$ is the reverse of the second connection from $g.v$ to $e.v$, followed by the edge from $e.v$ to $e.u$, followed by the first connection from $e.u$ to $g.u$; its orientation is read along the path as $g.u \leadsto e.u \leadsto e.v \leadsto g.v$. For the opposite direction, reverse this route. Thus every adjacency step of the original path can be replaced by a path in the new list, and concatenating these replacements proves reachability is preserved.

**Key facts.** `Kruskal.reach_mono`, `Kruskal.reach_of_mem`, `Kruskal.reach_symm`, `Kruskal.reach_lift`.
