<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.SixDisjointBlockChoice.tupleSymmDiff_incidentSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity of the incident supports

**Claim.** The symmetric difference of the four incident supports is empty.

**Proof.** For four sets, their tuple symmetric difference is the nested symmetric difference of the four sets (`tupleSymmDiff_finFour`). Fix an element $x$. If $x$ belongs to no chosen block, it belongs to no incident support, so it occurs zero times and is absent from the symmetric difference. Otherwise, choose a block containing $x$. Uniqueness of the block containing an element (`SixDisjointBlockChoice.eq_of_mem_blocks`) shows that this is the only block containing $x$. The element therefore lies in the incident supports of exactly the two endpoints of that edge, and in no others. Its even number of occurrences means it is absent from the symmetric difference. Since this holds for every element, the symmetric difference is empty.

**Key facts.** `FABL.tupleSymmDiff_finFour`, `FABL.SixDisjointBlockChoice.eq_of_mem_blocks`.
