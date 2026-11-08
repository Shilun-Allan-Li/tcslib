<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoInitial_remaining_disjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Block Coordinates

**Claim.** For any block and seed, the singleton containing the initial coordinate is disjoint from the set of the other two coordinates in that block.

**Proof.** Suppose a coordinate belongs to both sets. Membership in the singleton identifies it with the initial coordinate. Membership in the mapped set of remaining coordinates means it is the image, under the block embedding, of some leaf other than the seed. Since the embedding is injective, equality of the images forces that leaf to equal the seed, contradicting its exclusion from the seed-erased set. Thus the two sets are disjoint.
