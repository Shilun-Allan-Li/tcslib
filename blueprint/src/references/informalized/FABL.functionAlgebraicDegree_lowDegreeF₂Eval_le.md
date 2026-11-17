<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.functionAlgebraicDegree_lowDegreeF₂Eval_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for low-degree polynomials

**Claim.** The function formed by summing the given coefficients times their coordinate monomials has algebraic degree at most $\ell$.

**Proof.** By the coefficient formula for the algebraic normal form of a low-degree evaluation (`anfCoeff_lowDegreeF₂Eval`), its coefficients are the extended coefficient family: a set receives its assigned coefficient when its size is at most $\ell$, and zero otherwise. The algebraic-degree criterion (`algebraicDegree_le_iff`) says it suffices to show that every set with nonzero coefficient has size at most $\ell$. If a set had size greater than $\ell$, the extension rule would make its coefficient zero, a contradiction.

**Key facts.** `FABL.anfCoeff_lowDegreeF₂Eval`, `FABL.algebraicDegree_le_iff`.
