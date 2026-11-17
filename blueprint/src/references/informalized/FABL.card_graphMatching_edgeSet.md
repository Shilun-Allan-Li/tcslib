<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_graphMatching_edgeSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multipartite matching edge count

**Claim.** A perfect matching in the complete $2r$-partite graph with $k$ vertices in each part has exactly $rk$ edges.

**Proof.** Count incidences between parts and matching edges in two ways. Summing over parts, each part contributes $k$ incident matching edges by the part-edge count (card_graphMatchingPartEdges), so the total is $2rk$. Alternatively, sum over matching edges the number of parts to which each edge is incident. Every matching edge joins two vertices in distinct parts, so each contributes exactly $2$; hence this count is twice the number of matching edges. Equating the counts gives $2rk=2|E|$, and cancellation yields $|E|=rk$.

**Key facts.** `FABL.card_graphMatchingPartEdges`, `FABL.graphMatchingPartEdges_degree_two`.
