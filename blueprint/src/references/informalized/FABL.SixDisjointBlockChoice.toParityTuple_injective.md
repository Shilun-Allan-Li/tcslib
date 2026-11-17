<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.SixDisjointBlockChoice.toParityTuple_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the parity tuple map

**Claim.** The map sending six chosen disjoint blocks to their four incident supports is injective.

**Proof.** Suppose two choices have the same parity tuple. Equality of these tuples gives equality of their incident supports at every vertex. The blocks themselves can be recovered from the supports: for each edge, its block is the intersection of the supports at its two endpoints (`SixDisjointBlockChoice.block_eq_incidentSupport_inter`). Consequently, the two choices have the same block at every edge, so their lists of blocks agree. The extensionality result for block choices (`DisjointBlockChoices.ext_of_blocks_eq`) then implies that the choices are equal.

**Key facts.** `FABL.SixDisjointBlockChoice.block_eq_incidentSupport_inter`, `FABL.DisjointBlockChoices.ext_of_blocks_eq`.
