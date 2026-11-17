<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.exists_graphPartitePerfectMatching_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatible perfect matching

**Claim.** Under the given injectivity and even-fiber hypotheses, the complete multipartite graph has a perfect matching whose matched endpoints always carry the same label.

**Proof.** For each label $b$, let its fiber be the set of vertices carrying that label. This fiber is a clique in the complete multipartite graph: two distinct vertices with the same label cannot lie in the same part, since injectivity within that part would force them to be the same vertex. The fiber is finite, and its cardinality is even by hypothesis. The characterization of even cliques therefore supplies a matching covering every vertex in each fiber. Take the union of these matchings over all labels. Matchings from distinct fibers have disjoint vertex sets, so their union remains a matching; and every vertex belongs to the fiber of its own label, so the union is spanning. Thus it is perfect. Every edge in the union comes from the matching of one fiber, so its endpoints have the same label.
