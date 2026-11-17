<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/DirectionalDerivatives.lean :: FABL.booleanDerivative_eq_sum_anfMonomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative Expansion in Algebraic Normal Form

**Claim.** For every $x$, the derivative $f(x)+f(x+y)$ equals the sum over coordinate subsets $S$ of the ANF coefficient $a_S$ times the derivative of the monomial indexed by $S$.

**Proof.** Evaluate the function identity at an arbitrary $x$. The ANF expansion theorem (\(\texttt{anfEval_anfCoeff}\)) says that $f$ is the sum of its coefficients times the corresponding monomials; apply it at both $x$ and $x+y$. Substitute these two expansions into $f(x)+f(x+y)$. Distribute each coefficient across the two terms and regroup the finite sums. For each subset $S$, the resulting summand is its coefficient times the sum of the monomial’s values at $x$ and $x+y$, which is exactly that monomial’s Boolean derivative in direction $y$.

**Key facts.** `FABL.anfEval_anfCoeff`.
