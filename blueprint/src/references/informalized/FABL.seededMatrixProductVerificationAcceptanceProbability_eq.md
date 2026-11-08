<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.seededMatrixProductVerificationAcceptanceProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeded verification probability

**Claim.** For any seed map from $r$-bit strings to $\mathbb{F}_2^n$, the acceptance probability over a uniform seed string equals the acceptance probability under the uniform pushforward density.

**Proof.** Expectation under the uniform pushforward density equals the uniform expectation of the function evaluated at the image of the seed map (`FABL.ProbabilityDensity.expectation_uniformPushforward`). Rewriting the density-based acceptance probability by this identity reduces the claim to comparing the two acceptance indicators at each seed string. The seeded result is true exactly when the matrix verification predicate holds on the image (`FABL.seededMatrixProductVerificationResult_eq_true_iff`). Thus both indicators are one when the predicate holds and zero when it fails, so their expectations agree.

**Key facts.** `FABL.ProbabilityDensity.expectation_uniformPushforward`, `FABL.seededMatrixProductVerificationResult_eq_true_iff`.
