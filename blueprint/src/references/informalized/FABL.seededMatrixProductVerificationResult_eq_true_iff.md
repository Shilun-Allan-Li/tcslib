<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.seededMatrixProductVerificationResult_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeded Verification Criterion

**Claim.** The seeded verification test returns true exactly when, on the vector produced by the chosen seed string, every coordinate of $C'x$ agrees with the corresponding coordinate of $A(Bx)$.

**Proof.** By definition, the seeded result is the decision procedure applied to the verification predicate at the vector produced by the seed. A decidable proposition has decision value `true` exactly when the proposition holds. Applying this fact to the coordinatewise verification predicate gives the stated equivalence.
