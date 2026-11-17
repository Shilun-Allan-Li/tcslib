<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.depthTwoBlockModelValue_eq_majority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block Value Equals Majority

**Claim.** For each block, the depth-two block model's value equals the majority sign of the three entries in its recursive input block.

**Proof.** Unfold the block model: its value is the three-input pairwise majority applied to the entries at positions $0,1,2$ of the recursive input block. The fact that the three-input pairwise majority equals majority on the corresponding three-coordinate vector then identifies this with the majority of that recursive input block (\texttt{majorityThreePairValue\_eq\_majority}).

**Key facts.** `FABL.majorityThreePairValue_eq_majority`.
