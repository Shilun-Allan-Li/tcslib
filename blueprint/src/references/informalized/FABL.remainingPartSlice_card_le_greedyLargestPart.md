<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.remainingPartSlice_card_le_greedyLargestPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Largest Part Slice

**Claim.** The number of remaining vertices in any part is at most the number in the part selected to have largest slice size.

**Proof.** There are finitely many parts, and the positive assumption on $r$ ensures that there is at least one. Therefore the slice cardinalities attain a maximum. The greedy-selected part is chosen as a maximizer, so its slice cardinality is at least that of every part, including the specified one.
