<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.SixDisjointBlockChoice.incidentSupport_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of an incident support

**Claim.** For any vertex, the union of its three incident blocks has cardinality $3d$.

**Proof.** The incident support is the union of the blocks indexed by edges incident to the fixed vertex. These blocks are pairwise disjoint, since all distinct chosen blocks are pairwise disjoint (`SixDisjointBlockChoice.block_pairwiseDisjoint`). The cardinality of a finite union of pairwise disjoint sets is the sum of their cardinalities. Each block has cardinality $d$ (`SixDisjointBlockChoice.block_card`), and exactly three edges meet the vertex (`card_k4IncidentEdges`). Thus the sum is $d+d+d=3d$.

**Key facts.** `FABL.SixDisjointBlockChoice.block_pairwiseDisjoint`, `FABL.SixDisjointBlockChoice.block_card`, `FABL.card_k4IncidentEdges`.
