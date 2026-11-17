<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Basic.lean :: Kruskal.kruskal_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Kruskal output is a subset

**Claim.** Every edge returned by Kruskal’s algorithm on an input list occurs in that input list.

**Proof.** The membership property of edge processing (`processEdges_mem`) says that any edge in the final output either belonged to the initial accumulator or occurred in the list being processed. The accumulator here is empty, so only the second possibility remains: the edge occurs in the sorted input list. Sorting preserves membership in both directions, hence it occurs in the original input list.

**Key facts.** `Kruskal.processEdges_mem`.
