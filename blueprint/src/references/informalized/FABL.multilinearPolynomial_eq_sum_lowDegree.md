<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/IntegralThresholdRepresentations.lean :: FABL.multilinearPolynomial_eq_sum_lowDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expansion over Low-Degree Subsets

**Claim.** The multilinear polynomial with coefficient function supported on subsets of size at most $d$ evaluates at $x$ as the sum of its coefficients times the corresponding sign monomials over precisely those subsets.

**Proof.** Expand the polynomial as a sum over all subsets. For every subset outside the low-degree family, its coefficient is zero, so removing those terms does not change the sum. The remaining sum is indexed by members of the family. Attaching the family replaces each subset by the same subset together with its membership witness; on these attached terms the coefficient's conditional definition selects the given integer coefficient, viewed as a real number. This gives exactly the asserted sum.
