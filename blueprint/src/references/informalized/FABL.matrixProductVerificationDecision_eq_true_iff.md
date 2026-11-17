<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductVerificationDecision_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verification decision criterion

**Claim.** For every pair of matrices $A,B$, proposed product $C'$, and binary vector $x$, the verification decision accepts exactly when $(C'-AB)x=0$.

**Proof.** The decision is defined by deciding whether the verification predicate holds. A Boolean decision equals true exactly when its proposition holds. The predicate is equivalent to the statement that the difference matrix $C'-AB$ multiplied by $x$ is the zero vector (\texttt{FABL.matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero}); substituting this equivalence gives the criterion.

**Key facts.** `FABL.matrixProductVerificationPredicate_iff_difference_mulVec_eq_zero`.
