<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.lowDegreeF₂PolynomialLearnerLabeledOutputWithBackend_cubic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Backend Learner Output

**Claim.** For all $n,\ell,m\in\mathbb{N}$ and every list of $m$ labeled samples from $\{\pm1\}^n\times\{\pm1\}$, the low-degree polynomial learner using the cubic linear solver backend returns the same hypothesis as the learner using the default solver.

**Proof.** For the cubic backend, its solver is definitionally the default row solver. Substituting that backend into the backend-parameterized learner therefore reduces its output to the default learner's output, so the two hypotheses are equal.
