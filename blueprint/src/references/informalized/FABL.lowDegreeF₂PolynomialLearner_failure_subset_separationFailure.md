<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂PolynomialLearner_failure_subset_separationFailure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure implies separation failure

**Claim.** If the target has encoded algebraic degree at most $\ell$, then every sample list on which the learner fails to recover the encoded target is a list whose encoded inputs do not distinguish all low-degree coefficient families.

**Proof.** Take a sample list on which the learner fails. If its encoded inputs did distinguish all low-degree coefficient families, the exact-recovery theorem (`lowDegreeF₂PolynomialLearnerLabeledOutput_evaluate_eq`) would imply that the learner evaluates to the encoded target, contradicting failure. Hence separation fails for the encoded inputs. The definition of the sign-sample failure set identifies this condition with membership in that set, proving the inclusion.

**Key facts.** `FABL.lowDegreeF₂PolynomialLearnerLabeledOutput_evaluate_eq`.
