<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂PolynomialLearnerLabeledOutput_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact recovery from separating samples

**Claim.** If the encoded target has algebraic degree at most $\ell$ and the encoded sample inputs distinguish all low-degree coefficient families, then the low-degree polynomial learner trained on the target labels evaluates to the encoded target.

**Proof.** For each labeled example $(x,f(x))$, its binary encoding is the encoded input together with the encoded target value at that input; this is the identity `binaryLabeledSample_target`. Consequently, the learner’s training data are exactly the encoded target’s values on the encoded sample inputs. The recovery theorem for the elimination-based solver (`solveLowDegreeF₂Samples_evaluate_eq`) says that a degree-at-most-$\ell$ target is recovered from such samples whenever those inputs distinguish all low-degree coefficient families. Applying it gives the claimed equality of evaluations.

**Key facts.** `FABL.binaryLabeledSample_target`, `FABL.solveLowDegreeF₂Samples_evaluate_eq`.
