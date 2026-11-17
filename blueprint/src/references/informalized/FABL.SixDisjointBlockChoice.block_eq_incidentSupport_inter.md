<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.SixDisjointBlockChoice.block_eq_incidentSupport_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a block from its supports

**Claim.** For any edge of the complete graph on four vertices, its chosen block is the intersection of the incident supports at its two endpoints.

**Proof.** Fix an edge and an element $x$. If $x$ lies in the edge's block, that block appears in the union defining the incident support at each endpoint, so $x$ lies in their intersection. Conversely, if $x$ lies in both supports, it belongs to some block indexed by an edge incident to the first endpoint and some block indexed by an edge incident to the second. Uniqueness of the block containing an element (`SixDisjointBlockChoice.eq_of_mem_blocks`) forces those two edge indices to agree. Among the six edges of the complete graph on four vertices, the only edge incident to both endpoints of the fixed edge is that edge itself. Thus $x$ belongs to the fixed edge's block, proving the equality.

**Key facts.** `FABL.SixDisjointBlockChoice.eq_of_mem_blocks`.
