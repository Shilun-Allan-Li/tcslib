<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂MonomialCount_eq_sum_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Low-Degree Monomials

**Claim.** For every $n,\ell\in\mathbb{N}$, the number of subsets of $[n]$ of size at most $\ell$ is $\sum_{j=0}^{\ell}\binom{n}{j}$.

**Proof.** The monomial count is the cardinality of the subtype of subsets whose size is at most $\ell$. Thus it is the cardinality of that family of subsets. This family is exactly the low-degree Fourier family, whose cardinality is the sum of the numbers of subsets of each size $j$ from $0$ through $\ell$. The number of size-$j$ subsets of an $n$-element set is $\binom{n}{j}$, giving the formula.

**Key facts.** `FABL.card_lowDegreeFourierFamily_eq_sum_choose`.
