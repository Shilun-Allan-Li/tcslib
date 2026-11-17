<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.solveLowDegreeF₂Samples_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of a low-degree Boolean function

**Claim.** If $f$ has algebraic degree at most $\ell$ and the sample inputs separate degree-at-most-$\ell$ coefficient families, then the function represented by the solver’s output on $(x,f(x))$ equals $f$ on all inputs.

**Proof.** By the degree bound, the coefficient family representing $f$ satisfies all the sample equations (`FABL.coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows`). The solver’s consistency theorem therefore gives that its output coefficients satisfy those same equations (`FABL.solveLowDegreeF₂Samples_satisfies_of_exists`). The separation hypothesis then identifies the solver’s coefficients with the coefficients representing $f$ (`FABL.coefficients_eq_of_separates_of_satisfies`). Finally, the evaluation theorem for the coefficients of a degree-at-most-$\ell$ function (`FABL.lowDegreeF₂Eval_coefficientsOfFunction`) shows that this coefficient family evaluates to $f$ everywhere.

**Key facts.** `FABL.coefficientsOfFunction_satisfies_lowDegreeF₂SampleRows`, `FABL.solveLowDegreeF₂Samples_satisfies_of_exists`, `FABL.coefficients_eq_of_separates_of_satisfies`, `FABL.lowDegreeF₂Eval_coefficientsOfFunction`.
