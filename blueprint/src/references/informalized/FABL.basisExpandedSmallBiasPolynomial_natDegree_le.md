<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.basisExpandedSmallBiasPolynomial_natDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for the encoded polynomial

**Claim.** The natural degree of the basis-expanded polynomial is at most $n$.

**Proof.** The polynomial is a finite sum indexed by $i\in\mathrm{Fin}(n)$. Each summand is a scalar multiple of $X^{i+1}$, whose natural degree is at most $i+1$. Since $i<n$, we have $i+1\le n$. The degree of a finite sum is at most the maximum of the degrees of its summands, so the whole polynomial has natural degree at most $n$.
