<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInitial_subset_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Coordinate in Its Block

**Claim.** For any block and seed, the initial coordinate lies in the set of all three coordinates in that block.

**Proof.** The union of the initial singleton and the remaining coordinates is exactly the block's coordinate set, by the partition identity (`depthTwoInitial_union_remaining`). The initial singleton is contained in this union, so it is contained in the block's coordinate set.

**Key facts.** `FABL.depthTwoInitial_union_remaining`.
