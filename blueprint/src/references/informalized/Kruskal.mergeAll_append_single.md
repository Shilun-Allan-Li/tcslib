<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.mergeAll_append_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending one edge to a merge fold

**Claim.** Merging the edges of a list followed by a single edge $e$ has the same effect as first merging the list and then merging the endpoints of $e$.

**Proof.** Induct on the list $l$, allowing the initial union-find state to vary. For the empty list, both sides are precisely the state obtained by merging the endpoints of $e$ into the initial state. If $l$ begins with an edge $f$, folding $f$ first replaces the initial state by the state obtained by merging the endpoints of $f$; the induction hypothesis applied to this new state and the remaining list identifies both sides.
