<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.cubicLowDegreeF₂PolynomialLearnerWork_le_balancedCutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced Cutoff Learner Work Bound

**Claim.** At the cubic matrix-exponent cutoff, the degree-cutoff polynomial learner's work on the specified sample set is bounded by its certified coefficient times $(n+1)$ raised to the cutoff.

**Proof.** First identify the learner's work with the work of the same learner instantiated with the cubic linear-solver backend (\texttt{lowDegreeF₂PolynomialLearnerWorkWithBackend_cubic}). Then apply the general balanced-cutoff work bound for a backend equipped with an exponent certificate (\texttt{matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff}), using the cubic solver's certificate and its matrix exponent. This gives the stated coefficient and power bound.

**Key facts.** `FABL.lowDegreeF₂PolynomialLearnerWorkWithBackend_cubic`, `FABL.matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff`.
