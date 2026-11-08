<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearningAlgorithm.lean :: FABL.evaluate_lowDegreeJuntaHypothesisOfOutput_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the converted decision tree

**Claim.** If the binary decision tree computes $f$ after the binary-to-sign coordinate identification, then the sign-valued hypothesis tree obtained from it evaluates to $f$ on every sign vector.

**Proof.** To prove equality of the two functions, fix a sign vector $x$ and evaluate both sides there. Unfolding the definition of the converted tree's evaluation turns its input into the inverse binary encoding of $x`. The converted tree has the same evaluation as the original binary decision tree at every binary input (`DecisionTreeHypothesis.eval_ofF₂DecisionTree`). Apply the hypothesis that the original tree computes $f$ at this inverse encoding; the binary-to-sign equivalence sends that encoding back to $x`, yielding the desired value.

**Key facts.** `FABL.DecisionTreeHypothesis.eval_ofF₂DecisionTree`.
