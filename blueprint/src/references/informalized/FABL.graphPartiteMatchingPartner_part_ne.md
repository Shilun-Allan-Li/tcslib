<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphPartiteMatchingPartner_part_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Partners Lie in Different Parts

**Claim.** Every vertex and its matching partner belong to different parts of the complete $q$-partite graph.

**Proof.** The vertex and its partner are adjacent by the matching-partner adjacency property (`graphPartiteMatchingPartner_adj`). In a complete multipartite graph, adjacent vertices must have different part indices. Reversing that inequality gives the claimed order of the two indices.

**Key facts.** `FABL.graphPartiteMatchingPartner_adj`.
