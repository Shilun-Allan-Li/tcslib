<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂MonomialCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Number of Low-Degree Monomials

**Claim.** For every $n,\ell\in\mathbb{N}$, the number of subsets of $[n]$ of size at most $\ell$ is at most $(\ell+1)(n+1)^\ell$.

**Proof.** Rewrite the monomial count as the sum $\sum_{j=0}^{\ell}\binom{n}{j}$ using the counting identity. The low-degree Fourier family has this same cardinality, and its cardinality bound is $(\ell+1)(n+1)^\ell$. Substituting these cardinality expressions yields the desired inequality.

**Key facts.** `FABL.lowDegreeF₂MonomialCount_eq_sum_choose`, `FABL.card_lowDegreeFourierFamily_eq_sum_choose`, `FABL.card_lowDegreeFourierFamily_le`.
