<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.coefficients_eq_of_powerset_sum_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness from subset sums

**Claim.** Suppose two coefficient functions on subsets of $[n]$ have equal sums over the subsets of every $U\subseteq[n]$. Under the stated additive cancellation assumptions, the two coefficient functions are equal.

**Proof.** We prove equality of the coefficients by induction on a subset $S$, assuming equality has already been established for every proper subset of $S$. In the sum over all subsets of $S$, separate the term indexed by $S$ from the terms indexed by its proper subsets. The latter terms agree for the two coefficient functions by the induction hypothesis. The assumed equality of the full sums therefore leaves equality of the two terms indexed by $S$ after canceling the common tail. This proves equality at $S$; induction gives it for every subset, and hence the coefficient functions are equal.
