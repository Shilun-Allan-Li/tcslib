<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.combineJuntaAssignment_freePart_of_matches -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from fixed and free coordinates

**Claim.** If a sign vector agrees with a given assignment on $P$, then combining that assignment on $P$ with the vector's restriction to the complementary coordinates recovers the original vector.

**Proof.** Compare the two vectors coordinate by coordinate. For a coordinate in $P$, the combined vector uses the given assignment, which equals the original vector there by hypothesis. For a coordinate outside $P$, it uses the restriction of the original vector, so again the values agree. Since the values agree at every coordinate, the vectors are equal.
