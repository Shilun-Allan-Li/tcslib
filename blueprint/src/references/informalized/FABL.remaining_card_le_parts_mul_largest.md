<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.remaining_card_le_parts_mul_largest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Largest part bound

**Claim.** The size of the finite set of vertices is at most the number of parts times the number of its vertices in a largest part.

**Proof.** The parts partition the vertex set, so the total number of vertices is the sum of the slice sizes over all $2r$ parts (`sum_card_remainingPartSlice`). By maximality of the chosen part, each slice has size at most the size of that largest slice (`remainingPartSlice_card_le_greedyLargestPart`). Summing these $2r$ inequalities bounds the total by $2r$ copies of the largest slice, which is the asserted bound.

**Key facts.** `FABL.sum_card_remainingPartSlice`, `FABL.remainingPartSlice_card_le_greedyLargestPart`.
