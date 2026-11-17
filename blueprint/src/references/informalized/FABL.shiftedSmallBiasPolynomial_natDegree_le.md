<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.shiftedSmallBiasPolynomial_natDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for the Shifted Polynomial

**Claim.** For every binary vector γ of length n, the shifted small-bias polynomial has natural degree at most n − 1.

**Proof.** The polynomial is a finite sum indexed by $i\in\mathrm{Fin}(n)$, whose $i$th summand is a scalar multiple of $X^i$. Each such summand has natural degree at most $i$. Since $i<n$, its degree is at most $n-1$. The degree of a finite sum is at most the maximum of the degrees of its summands, so the whole polynomial has natural degree at most $n-1$.
