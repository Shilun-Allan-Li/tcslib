<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.binaryCubeSignEquiv_combineJuntaF₂Assignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding of Combined Assignments

**Claim.** Encoding the binary vector formed from assignments on a coordinate set and its complement gives the same sign vector as combining the separately encoded assignments.

**Proof.** It suffices to compare the two sign vectors at each coordinate. If the coordinate belongs to $P$, the combined binary vector takes its value from $z$, and the combined sign vector takes its value from the sign encoding of that same entry. The coordinate formula for the sign encoding (`FABL.binaryCubeSignEquiv_apply`) identifies these values. If the coordinate is outside $P$, both constructions instead use the corresponding entry of $y$, and the same coordinate formula gives equality. Thus the sign vectors agree at every coordinate.

**Key facts.** `FABL.binaryCubeSignEquiv_apply`.
