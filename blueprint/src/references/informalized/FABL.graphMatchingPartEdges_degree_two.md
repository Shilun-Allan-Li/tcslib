<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingPartEdges_degree_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Parts Incident to Each Matching Edge

**Claim.** For any matching edge, exactly two parts are incident to it, so the set of such parts has cardinality $2$.

**Proof.** Write the edge’s endpoints as $u$ and $v$. Since it belongs to the complete multipartite graph, their parts differ. By the characterization of incidence with a part (mem_graphMatchingPartEdges_iff), a part is counted precisely when one of its vertices occurs as an endpoint of the edge. Thus the counted parts are exactly the parts of $u$ and $v$: each endpoint supplies its own position witnessing incidence, and any incidence witness must identify its part with one of these endpoint parts. The set is therefore the two-element set consisting of those distinct parts, and has cardinality $2$.

**Key facts.** `FABL.mem_graphMatchingPartEdges_iff`.
