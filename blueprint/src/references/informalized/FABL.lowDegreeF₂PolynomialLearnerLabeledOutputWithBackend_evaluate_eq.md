<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact recovery with a backend

**Claim.** If the encoded target has algebraic degree at most $\ell$ and the encoded sample inputs distinguish all low-degree coefficient families, then the backend learner trained on the target labels evaluates to the encoded target.

**Proof.** The binary encoding of each labeled sample $(x,f(x))$ is exactly the pair consisting of the encoded input and the encoded target value there (the sample-encoding identity, `binaryLabeledSample_target`). Thus the learner receives precisely the samples obtained by evaluating the encoded target on the encoded inputs. The backend recovery theorem (`solveLowDegreeF₂SamplesWithBackend_evaluate_eq`) applies: the degree bound makes the encoded target representable by a low-degree coefficient family, and separation ensures that the sample values determine that family uniquely. Since the backend returns a solution to any consistent sample system, the learner’s evaluation agrees everywhere with the encoded target.

**Key facts.** `FABL.binaryLabeledSample_target`, `FABL.solveLowDegreeF₂SamplesWithBackend_evaluate_eq`.
