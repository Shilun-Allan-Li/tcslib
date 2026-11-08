<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.solveLowDegreeF₂Samples_satisfies_of_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consistency of the sample solver

**Claim.** If some degree-at-most-$\ell$ coefficient family satisfies every equation determined by the samples, then the coefficient family returned by the specified solver satisfies every one of those equations.

**Proof.** Regard the degree-at-most-$\ell$ coefficient families as assignments to the finite set of low-degree monomials. The assumed family witnesses consistency of the sample-equation system. The general consistency theorem for `solveF₂Rows` (`FABL.solveF₂Rows_satisfies_of_exists`) says that the specified solver’s assignment satisfies every row whenever such a witness exists. By definition, the sample solver uses this assignment as its output coefficient family, giving the claim.

**Key facts.** `FABL.solveF₂Rows_satisfies_of_exists`.
