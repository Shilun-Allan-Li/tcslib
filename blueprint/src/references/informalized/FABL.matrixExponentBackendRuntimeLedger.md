<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.matrixExponentBackendRuntimeLedger -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runtime and Exponent Bounds

**Claim.** Given a positive rational matrix exponent $\omega$, a backend certificate with exponent at least $2$ and its stated runtime guarantee, and the specified sample list, the learner's work is at most the certificate-dependent coefficient times $(n+1)$ raised to the cutoff. Also, the maximum of the solver exponent and the cutoff is strictly less than $\bigl(\omega/(\omega+1)\bigr)k+1$.

**Proof.** Apply the backend runtime bound at degree $k-\text{cutoff}$ and the prescribed dimension and row coefficients; the balanced-cutoff work estimate gives the claimed upper bound on the learner's total work. Separately, the combined-exponent estimate states that the maximum of the solver exponent and the cutoff is strictly below the displayed fractional bound. Pairing these two estimates proves both conjuncts.

**Key facts.** `FABL.matrixExponentLowDegreeF₂WorkWithBackend_le_balancedCutoff`, `FABL.matrixExponentJuntaCombinedExponent_lt_fraction_add_one`.
