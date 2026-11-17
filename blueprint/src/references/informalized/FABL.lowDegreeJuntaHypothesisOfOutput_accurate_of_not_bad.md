<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearningAlgorithm.lean :: FABL.lowDegreeJuntaHypothesisOfOutput_accurate_of_not_bad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accuracy of a Good Output Hypothesis

**Claim.** If the learner's output is not bad, then the hypothesis obtained from that output has relative Hamming distance at most the accuracy parameter from the target.

**Proof.** Split according to whether the output is absent or is a tree. If it is absent, it is bad by definition, contradicting the assumption that the output is not bad. Thus the output is a tree, and not being bad means that this tree computes the target on every input. The evaluation identity for a correctly computing tree (`evaluate_lowDegreeJuntaHypothesisOfOutput_eq`) then says that the hypothesis obtained from the output is exactly the target. Their Hamming distance is consequently zero, so their relative Hamming distance is zero as well. Since the accuracy parameter is nonnegative, this distance is at most that parameter.

**Key facts.** `FABL.evaluate_lowDegreeJuntaHypothesisOfOutput_eq`.
