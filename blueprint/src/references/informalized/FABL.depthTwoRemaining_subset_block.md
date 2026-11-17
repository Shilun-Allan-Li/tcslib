<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoRemaining_subset_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Remaining coordinates stay in the block

**Claim.** For any block and seed in $\{0,1,2\}$, the block's coordinates other than the one selected first by the seed are contained in the full set of coordinates of that block.

**Proof.** The initial coordinate together with the remaining coordinates is exactly the full coordinate set of the block, by the initial-union-remaining identity. Therefore the remaining coordinates are contained in that union, and hence in the full block coordinate set.

**Key facts.** `FABL.depthTwoInitial_union_remaining`.
