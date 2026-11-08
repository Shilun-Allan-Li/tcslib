<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.variance_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a dictator

**Claim.** For every coordinate $i$, the dictator function $\chi_i$ has variance $1$.

**Proof.** The real-valued dictator is the singleton Fourier monomial at $\{i\}$ (`dictator_toReal_eq_monomial_singleton`). The variance Fourier formula (`variance_eq_sum_sq_fourierCoeff`) expresses its variance as its second moment minus the square of its mean. Each value of this monomial squares to $1$ (`monomial_sq`), so its second moment is $1$. Its mean is zero: the expectation of a nonempty Fourier monomial vanishes (`expect_monomial`). Therefore its variance is $1-0^2=1$.

**Key facts.** `FABL.dictator_toReal_eq_monomial_singleton`, `FABL.variance_eq_sum_sq_fourierCoeff`, `FABL.monomial_sq`, `FABL.expect_monomial`.
