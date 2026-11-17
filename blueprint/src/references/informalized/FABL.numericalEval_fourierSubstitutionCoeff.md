<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/FourierToF₂Polynomial.lean :: FABL.numericalEval_fourierSubstitutionCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of Fourier substitution coefficients

**Claim.** Evaluating the coefficient function defined by the weighted sums of Fourier coefficients over supersets in the squarefree indicator monomials gives $p$ composed with the coordinatewise binary-to-sign map.

**Proof.** Fix a binary vector $x$. The Fourier expansion of $p$ at the corresponding sign vector expresses its value as the sum, over all sets $S$, of the Fourier coefficient at $S$ times the sign monomial at $S$ (`fourier_expansion`). Expand each such sign monomial in numerical monomials indexed by subsets $T\subseteq S$ (`monomial_binaryCubeSignEquiv_eq_numerical_sum`). This yields a finite sum over pairs $(S,T)$ with $T\subseteq S$. Reordering the sums groups terms by $T$. For each fixed $T$, its common factor $(-2)^{|T|}$ and its numerical monomial at $x$ can be taken outside the sum over all $S\supseteq T$. The remaining sum is exactly the one defining the Fourier-substitution coefficient at $T$. Summing over $T$ is therefore the numerical evaluation of that coefficient function, proving the claimed identity at every $x$.

**Key facts.** `FABL.fourier_expansion`, `FABL.monomial_binaryCubeSignEquiv_eq_numerical_sum`.
