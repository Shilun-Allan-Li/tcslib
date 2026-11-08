<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.seededMatrixProductVerificationAcceptanceProbability_boolVector_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeded and uniform verification probabilities

**Claim.** For the seed that maps each Boolean vector coordinatewise to $\mathbb{F}_2^n$, the seeded verification acceptance probability equals the acceptance probability for a uniform vector in $\mathbb{F}_2^n$.

**Proof.** The coordinatewise Boolean-to-$\mathbb{F}_2$ map is an equivalence, so finite expectation is unchanged when the uniform average is reindexed along it (`Fintype.expect_equiv`). For each Boolean vector, the seeded result is true exactly when the matrix verification predicate holds on its image (`FABL.seededMatrixProductVerificationResult_eq_true_iff`). Therefore the two summands agree: when the predicate holds both acceptance indicators equal one, and when it fails both equal zero. The reindexed expectations, and hence the two probabilities, are equal.

**Key facts.** `FABL.seededMatrixProductVerificationResult_eq_true_iff`.
