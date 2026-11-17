<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.computesJuntaRestriction_of_not_outputBad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision Tree Computes the Junta Restriction

**Claim.** If a decision tree querying only coordinates outside $P$ is not classified as a bad output for $(f,P,z)$, then on every binary input whose sign vector agrees with $z$ on $P$, the tree returns the value of $f$ at that sign vector.

**Proof.** For the given tree, being classified as a bad output means precisely that it does not compute the junta restriction. The hypothesis that it is not bad therefore negates this failure condition, yielding exactly the defining property: on every input matching $z$ on $P$, the tree's output equals the target function's value.
