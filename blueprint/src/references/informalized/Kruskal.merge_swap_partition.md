<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.merge_swap_partition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Order Independence of Two Merges

**Claim.** Merging the endpoints of two weighted edges in either order yields states that induce the same partition of the nodes.

**Proof.** Fix two nodes $i,j$. Split into cases according to whether each node initially has the same representative as the first endpoint of the first edge. In each case, evaluate the two successive merges in both orders. A merge changes precisely the representatives in the component of its second endpoint, assigning them the first endpoint’s representative; tracking these changes shows that the final equality of the representatives of $i$ and $j$ agrees in the two orders. Hence the resulting states induce the same partition.
