<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.boolean_variance_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance bound for Boolean functions

**Claim.** A Boolean-valued function on a finite product probability space has variance at most $1$.

**Proof.** First express the variance as the sum over all subsets of the squared expectations of the function’s components, omitting the empty-set component (`variance_eq_sum_components`). Each summand is nonnegative: for a nonempty subset it is an expectation of a square, and for the empty subset the displayed summand is zero. Thus this sum is at most the same sum with every component included. By Parseval’s identity (`FiniteProduct.parseval`), the latter is the expectation of $f^2$. Since $f$ takes only the values $-1$ and $1$, its square is constantly $1$; the expectation of a constant is that constant (`FiniteProduct.expect_const`). Therefore the variance is at most $1$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.variance_eq_sum_components`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.
