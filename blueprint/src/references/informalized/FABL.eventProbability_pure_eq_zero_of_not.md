<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.eventProbability_pure_eq_zero_of_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pure Output Has Zero Bad Probability

**Claim.** If a learning program returns a fixed output that does not satisfy a predicate, then the probability that its output satisfies that predicate is zero.

**Proof.** A pure program has the point-mass law at the fixed output, paired with zero cost. Since the predicate fails at that output, the event contains no point in the support of this law. Evaluating the event probability under this point mass therefore gives zero.
