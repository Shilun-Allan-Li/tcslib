<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.matchedJuntaRestrictionExample_label -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Label of a Restricted Example

**Claim.** If a sample matches the fixed assignment on $P$ and its label is the value of $f$ at its input, then its label equals the restriction of $f$ evaluated at the sample’s free-coordinate assignment.

**Proof.** The label of the restricted example is the original sample label, while its free-coordinate assignment is the free part of the original input. Since that input matches the fixed assignment on $P$, combining the fixed assignment with its free part reconstructs the original input (`combineJuntaAssignment_freePart_of_matches`). Evaluating the restriction at the free part therefore evaluates $f$ at the original input, which equals the label by hypothesis.

**Key facts.** `FABL.combineJuntaAssignment_freePart_of_matches`.
