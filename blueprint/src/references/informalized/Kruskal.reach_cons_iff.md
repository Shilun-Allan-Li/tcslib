<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.reach_cons_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability after adding one edge

**Claim.** Two vertices are connected through a list with a single edge prepended exactly when they were already connected through the remaining list, or their path can use the new edge to join paths in the remaining list in one of its two orientations.

**Proof.** First, every path through `rest` remains a path through `g :: rest`, because adding an edge preserves all earlier adjacencies. The new edge also gives a path from `g.u` to `g.v`, and symmetry gives one in the reverse direction. Thus each of the three stated alternatives yields a path through the enlarged list by concatenating the relevant paths.

For the converse, induct on a path through `g :: rest`, considering its final adjacency. If that adjacency uses an edge of `rest`, the induction hypothesis decomposes the preceding path into the three alternatives. The final adjacency can then be appended to the appropriate path segment; when its orientation is reversed, use symmetry of reachability in `rest` to reverse that edge's endpoint connection before concatenating. If the final adjacency is the new edge `g`, its orientation determines whether the path has just reached `g.u` or `g.v`. Applying the induction hypothesis to the preceding path and using the new edge (or its reverse) gives one of the same three alternatives. This proves the characterization in both directions.

**Key facts.** `Kruskal.reach_mono`, `Kruskal.reach_of_mem`, `Kruskal.reach_symm`.
