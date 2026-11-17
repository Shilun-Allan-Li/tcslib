<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.anfCoeff_univ_eq_sum_f₂BooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total ANF coefficient sum

**Claim.** The sum of all algebraic normal form coefficients of $f$ equals the sum of the values of $f$ over all inputs in the cube.

**Proof.** By the definition of the coefficients, their sum over all subsets is the sum, over each subset $T\subseteq[n]$, of $f$ evaluated at the cube point whose support is $T$. The equivalence between cube points and subsets, given by taking support and its inverse, lets us reindex this finite sum by cube points. Under this reindexing, the point associated to the support of $x$ is exactly $x$, so the resulting sum is $\sum_x f(x)$.
