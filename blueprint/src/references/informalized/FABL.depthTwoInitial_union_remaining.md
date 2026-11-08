<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInitial_union_remaining -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition of a Block

**Claim.** For any block and seed, the initial coordinate together with the other two coordinates is exactly the set of all three coordinates in that block.

**Proof.** Each coordinate in the block is the image of a leaf index under the block embedding. The three leaf indices split into the seed itself and the indices other than the seed. Their images therefore split into the image of the seed, which is the initial singleton, and the images of the other leaves, which form the remaining-coordinate set. Hence their union is precisely the block's coordinate set.
