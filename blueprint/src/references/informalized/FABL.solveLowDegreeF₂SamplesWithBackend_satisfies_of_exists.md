<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.solveLowDegreeF₂SamplesWithBackend_satisfies_of_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backend solution of consistent sample equations

**Claim.** If some degree-at-most-$\ell$ coefficient family satisfies every equation determined by the samples, then the family returned by the backend also satisfies every such equation.

**Proof.** Apply the backend’s defining consistency guarantee to the list of sample equations and the assumed satisfying coefficient family. It states directly that the coefficient family returned by the backend satisfies every equation in that list.
