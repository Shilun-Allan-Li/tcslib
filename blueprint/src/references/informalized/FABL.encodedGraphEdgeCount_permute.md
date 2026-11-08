<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.encodedGraphEdgeCount_permute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Edge Count Under Vertex Relabeling

**Claim.** Permuting the vertices of an encoded graph leaves its number of edges unchanged.

**Proof.** The edge count is the sum, over all two-element vertex subsets, of $1$ when the graph marks that subset as present and $0$ otherwise. Relabeling evaluates the original graph at the inverse image of each edge. The induced map on two-element subsets is a bijection, so reindexing this finite sum by that bijection leaves its value unchanged.
