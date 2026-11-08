<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂Eval_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Low-Degree Evaluation

**Claim.** For all $n$ and $\ell$, evaluating the sum of two coefficient families on the $n$-dimensional Boolean cube over $\mathbb F_2$, using monomials of degree at most $\ell$, gives the sum of their evaluations at every input.

**Proof.** Fix an input $x$. In each monomial term, multiplication distributes over the sum of the two coefficients. Summing these termwise identities over all monomials of degree at most $\ell$ separates the sum into the evaluation of the first coefficient family plus the evaluation of the second. Since this holds for every $x$, the evaluated functions are equal.
