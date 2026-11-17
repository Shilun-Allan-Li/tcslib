<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.eval_depthTwoFinishDifferent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Different-Value Finish

**Claim.** When the two supplied initial signs differ, the combined finish tree evaluates to the majority-pair value of the outputs of its first, second, and third component trees.

**Proof.** Each component tree has outputs in the two-element sign set, as do the supplied signs. Split into the possible sign values for the two supplied signs and for the three component-tree outputs. In each case, the construction first evaluates the third tree, then uses the inequality of the supplied signs to choose the appropriate order for running the first two component trees. The disjointness hypotheses ensure those component queries can be combined as specified; the resulting branches either return the repeated sign when two outputs agree or return the remaining output. This is exactly the defining majority-pair value. The finite case check establishes the equality for every possible choice of signs.

**Key facts.** `FABL.FiniteDecisionTree.eval_castAvailable`, `FABL.FiniteDecisionTree.eval_mapOutput`, `FABL.FiniteDecisionTree.eval_thenOnDisjoint`.
