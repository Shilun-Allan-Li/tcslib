<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaMatchCount_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Count as an Indicator Sum

**Claim.** The number of samples whose coordinates on $P$ agree with $z$ equals the sum over the batch of the indicator that each sample agrees with $z$ on $P$.

**Proof.** The matching count is the cardinality of the filtered set of indices whose fixed parts equal $z$. The cardinality of a finite filtered set is the sum of the indicators of its membership condition. For each index, equality of the fixed parts is equivalent to agreement at every coordinate of $P$: evaluating the equality gives coordinatewise agreement, and conversely coordinatewise agreement gives equality of the assignments. The resulting indicators are exactly those of the stated matching condition, giving the formula.
