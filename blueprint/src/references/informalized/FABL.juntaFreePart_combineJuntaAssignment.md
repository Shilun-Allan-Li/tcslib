<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaFreePart_combineJuntaAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the Free Assignment

**Claim.** If the fixed assignment on $P$ and the free assignment outside $P$ are combined into a sign vector, restricting that vector to the coordinates outside $P$ recovers the free assignment.

**Proof.** Two assignments on the complement of $P$ are equal once they agree at every coordinate there. Fix such a coordinate. It does not belong to $P$, so the combined vector takes its value from the free assignment. Hence the restriction agrees with the free assignment at every coordinate.
