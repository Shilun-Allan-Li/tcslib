<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.DisjointBlockChoices.blocks_pairwiseDisjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairwise disjointness of chosen blocks

**Claim.** The blocks in the list associated with any valid sequence of successive disjoint choices are pairwise disjoint.

**Proof.** Induct on the number of choices. The empty list is pairwise disjoint. At a successor step, write the choice as a first block followed by the remaining choices. The induction hypothesis says that the blocks chosen in the remainder are pairwise disjoint. Moreover, every block in their list is contained in the set remaining after the first block is removed (`DisjointBlockChoices.blocks_subset`). Thus it is disjoint from the first block, since that remaining set is the original set with the first block removed. The first block is therefore disjoint from every later block, and the later blocks are pairwise disjoint among themselves.

**Key facts.** `FABL.DisjointBlockChoices.blocks_subset`.
