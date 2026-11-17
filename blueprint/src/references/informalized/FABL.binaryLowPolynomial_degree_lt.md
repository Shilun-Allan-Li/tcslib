<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryLowPolynomial_degree_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for the coefficient polynomial

**Claim.** For every natural number $\ell$ and every coefficient vector of length $\ell$, the degree of its low polynomial is strictly less than $\ell$.

**Proof.** Apply the finite-sum degree bound for a sum indexed by $\mathrm{Fin}\,\ell$ (`Polynomial.degree_sum_fin_lt`): each summand is a coefficient times $X^i$ for an index $i<\ell$, so its degree is at most $i$, and hence strictly below $\ell$. The sum therefore has degree strictly below $\ell.
