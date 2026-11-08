<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaFixedPart_combineJuntaAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the Fixed Assignment

**Claim.** If the fixed assignment on $P$ and the free assignment outside $P$ are combined into a sign vector, restricting that vector to $P$ recovers the fixed assignment.

**Proof.** Two assignments on $P$ are equal once they agree at every coordinate. Fix a coordinate in $P$. In the combined vector, the membership condition holds, so its value there is taken from the fixed assignment. Thus the restriction agrees with the fixed assignment at every coordinate, proving equality.
