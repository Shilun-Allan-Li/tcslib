<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixExponentSolver.lean :: FABL.solveLowDegreeF₂SamplesWithBackend_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery from separating samples

**Claim.** If $f$ has algebraic degree at most $\ell$ and the sample inputs separate degree-at-most-$\ell$ coefficient families, then the polynomial represented by the backend solver’s output on $(x,f(x))$ agrees with $f$ everywhere.

**Proof.** The degree bound ensures that the coefficient family representing $f$ satisfies every sample equation (`FABL.coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows`). Thus the system is consistent, and the backend’s consistency guarantee implies that its output coefficients also satisfy every sample equation (`FABL.solveLowDegreeF₂SamplesWithBackend_satisfies_of_exists`). Separation now forces those output coefficients to equal the coefficients representing $f$ (`FABL.coefficients_eq_of_separates_of_satisfies`). Evaluating both sides, the representation theorem for a degree-at-most-$\ell$ function (`FABL.lowDegreeF₂Eval_coefficientsOfFunction`) identifies the resulting polynomial with $f$ at every input.

**Key facts.** `FABL.coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows`, `FABL.solveLowDegreeF₂SamplesWithBackend_satisfies_of_exists`, `FABL.coefficients_eq_of_separates_of_satisfies`, `FABL.lowDegreeF₂Eval_coefficientsOfFunction`.
