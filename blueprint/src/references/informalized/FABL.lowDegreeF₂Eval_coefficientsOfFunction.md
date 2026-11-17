<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂Eval_coefficientsOfFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery from Low-Degree Coefficients

**Claim.** If a Boolean function over $\mathbb F_2$ has algebraic degree at most $\ell$, then evaluating its algebraic normal form coefficients on monomials of degree at most $\ell$ recovers the function at every input.

**Proof.** Fix an input $x$. First identify the sum over low-degree monomials with the sum over the corresponding family of subsets. This family is contained in the family of all subsets. In the full sum, every omitted subset has size greater than $\ell$; the degree bound, by the characterization of algebraic degree ($\texttt{algebraicDegree\_le\_iff}$), forces its coefficient to be zero. Adding these zero terms therefore turns the low-degree sum into the full algebraic normal form evaluation. The algebraic normal form coefficients recover the function ($\texttt{anfEval\_anfCoeff}$), so the result at $x$ is $f(x)$.

**Key facts.** `FABL.algebraicDegree_le_iff`, `FABL.anfEval_anfCoeff`.
