<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.anfEval_extendLowDegreeF₂Coefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after extending low-degree coefficients

**Claim.** Extending coefficients of subsets of size at most $\ell$ by zero on larger subsets yields the same evaluation as summing only over subsets of size at most $\ell$.

**Proof.** Fix an input $x$. In the full evaluation sum, every set of size greater than $\ell$ contributes zero by the definition of the extension. Therefore the sum reduces to sets of size at most $\ell$. Reindex those sets by the subtype consisting of a set together with its proof that its size is at most $\ell$. On this subtype, the extended coefficient is the original coefficient. The resulting sum is exactly the low-degree evaluation at $x$. Since this holds at every input, the functions agree.
