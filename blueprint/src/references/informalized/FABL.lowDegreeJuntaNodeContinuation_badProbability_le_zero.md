<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaNodeContinuation_badProbability_le_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Bad-Decision Probability

**Claim.** If the supplied sample is not bad for the node procedure, then the continuation’s probability of returning a bad decision is at most zero.

**Proof.** Split on whether the sample is absent. If it is absent, the continuation returns `none`, which is not a bad outcome under the assumed goodness condition. If it is a batch, project it to the restricted batch used by the continuation. The goodness hypothesis then says that this batch is not bad, so the decision produced from it is correct. The continuation returns that decision deterministically, with only a work charge added to the outcome. Hence the event of returning a bad decision has probability zero, and therefore probability at most zero.
