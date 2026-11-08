<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.JuntaNodeDecision.isCorrect_of_not_isBad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of a Nonbad Decision

**Claim.** A decision that is not bad is correct: a constant decision agrees with the entire restricted target, and a coordinate decision identifies a coordinate on which the restriction genuinely depends.

**Proof.** For a decision supplied as a `some` value, being bad means precisely that the decision is not correct. The hypothesis that it is not bad therefore rules out the negation of correctness, and hence the decision is correct. Unpacking the definition of correctness gives the stated conclusion in either the constant or coordinate case.
