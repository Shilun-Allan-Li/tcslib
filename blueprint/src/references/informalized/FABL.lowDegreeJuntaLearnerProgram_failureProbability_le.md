<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaLearnerProgram_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Junta Learner Failure Bound

**Claim.** For a Boolean function that is a $k$-junta, the recursive learner built from a relevant-coordinate finder returns a decision tree computing the target, except with probability at most the prescribed failure parameter.

**Proof.** The learner is exactly the recursive junta learner built from the given relevant-coordinate finder, with the same target, junta size bound, and failure parameter. The recursive learner failure theorem (`FABL.recursiveJuntaLearner_failureProbability_le`) states that for any such finder, on any $k$-junta, the probability that the learner returns no tree or a tree that fails to compute the target is at most the failure parameter. Applying that theorem to this finder gives the claimed bound.

**Key facts.** `FABL.recursiveJuntaLearner_failureProbability_le`.
