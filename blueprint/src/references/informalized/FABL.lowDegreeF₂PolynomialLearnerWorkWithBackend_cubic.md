<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.lowDegreeF₂PolynomialLearnerWorkWithBackend_cubic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic backend work identity

**Claim.** For any $n,\ell,m$ and any list of $m$ labeled examples, the work charged to the learner using the cubic backend equals the work charged to the learner using the specified elimination procedure.

**Proof.** Expand the backend learner’s work definition: it charges the sample-processing term and the backend’s solver work. For the cubic backend, that solver work is the elimination procedure’s work plus the number of pivots times the number of coordinates plus one. The specified learner’s work has the same sample-processing term and the same elimination and pivot terms, since the coordinate count is the number of low-degree monomials. Rearranging the natural-number additions gives the asserted identity.
