<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_depthTwoInitialTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Tree Query Count

**Claim.** For every block, seed, and sign-valued input, the depth-two initial tree makes exactly one query.

**Proof.** The initial tree is a single query at the designated coordinate, followed immediately by a leaf for either possible observed sign. Its query trace therefore consists of that one coordinate, so its length, and hence its query count, is exactly one.
