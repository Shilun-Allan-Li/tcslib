<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.scheduledLowDegreeF₂PolynomialLearnerProgram_failureProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Learner Failure Bound

**Claim.** If the target’s Boolean encoding has algebraic degree at most $\ell$, then the scheduled low-degree polynomial learner’s failure probability is at most $\delta$.

**Proof.** Let $m$ be the scheduled sample count. The run law for the learner identifies its output distribution with the image of a uniform batch of $m$ inputs (`FABL.runWithCost_lowDegreeF₂PolynomialLearnerProgram`). Rewriting the failure event under this image law reduces its probability to the measure of the set of input batches on which the learner’s output differs from the target encoding. The learner’s failure-set inclusion places this set inside the separation-failure set for degree at most $\ell$ (`FABL.lowDegreeF₂PolynomialLearner_failure_subset_separationFailure`). Monotonicity of measure bounds the learner’s failure probability by the measure of that larger set, and the scheduled separation-failure bound makes the latter at most $\delta$ (`FABL.measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le`).

**Key facts.** `FABL.runWithCost_lowDegreeF₂PolynomialLearnerProgram`, `FABL.lowDegreeF₂PolynomialLearner_failure_subset_separationFailure`, `FABL.measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le`.

**Caveat.** The supplied informal statement describes a different learning exercise. This account follows the formal theorem and its proof source.
