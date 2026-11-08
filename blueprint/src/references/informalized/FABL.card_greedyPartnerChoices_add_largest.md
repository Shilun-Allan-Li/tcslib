<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_greedyPartnerChoices_add_largest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Greedy choice count decomposition

**Claim.** For a nonempty finite set of vertices, the number lying outside the part chosen by the greedy pivot plus the number lying in the chosen largest part equals the total number of vertices.

**Proof.** The greedy pivot lies in the part selected as largest (`greedyPivot_part`). Thus the vertices counted among the greedy partner choices are exactly those outside that part, while the part slice counts those inside it. These two complementary subsets partition the remaining vertices, so their cardinalities sum to the cardinality of the whole set.

**Key facts.** `FABL.greedyPivot_part`.
