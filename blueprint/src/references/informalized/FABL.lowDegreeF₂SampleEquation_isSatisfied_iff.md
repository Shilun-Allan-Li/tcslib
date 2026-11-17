<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂SampleEquation_isSatisfied_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sample equation satisfaction criterion

**Claim.** A coefficient family satisfies the linear equation associated with a labeled sample $(x,b)$ exactly when its low-degree polynomial evaluates at $x$ to $b$.

**Proof.** The sample equation assigns to each monomial coordinate its value at $x$ and has constant term $b$. Evaluating its left-hand side on the coefficient family gives the sum, over all monomials of degree at most $\ell$, of the coefficient times that monomial’s value at $x$. This is precisely the low-degree polynomial evaluation; commutativity of multiplication in $\mathbb F_2$ puts the factors in the same order as in the polynomial definition. Thus equation satisfaction is equivalent to that evaluation equaling $b$.
