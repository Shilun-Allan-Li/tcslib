<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.SixDisjointBlockChoice.block_pairwiseDisjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairwise disjointness of chosen blocks

**Claim.** Any two blocks with distinct indices are disjoint.

**Proof.** The list of blocks extracted from a choice is pairwise disjoint (`DisjointBlockChoices.blocks_pairwiseDisjoint`). The block at an index is the list entry at that index. Therefore, when the first index is less than the second, the list's pairwise disjointness gives the desired disjointness. When the second index is less than the first, apply the same fact in the reverse order and use symmetry of disjointness.

**Key facts.** `FABL.DisjointBlockChoices.blocks_pairwiseDisjoint`.
