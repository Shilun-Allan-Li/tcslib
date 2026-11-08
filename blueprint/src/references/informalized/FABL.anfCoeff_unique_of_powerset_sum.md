<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ANF.lean :: FABL.anfCoeff_unique_of_powerset_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness from powerset sums

**Claim.** If two coefficient families have equal sums over the subsets of every finite coordinate set, then the coefficient families are equal.

**Proof.** Apply the general coefficient-uniqueness result for powerset sums: in a right-cancellative additive commutative monoid, equality of all sums over subsets forces equality of the individual coefficients (`coefficients_eq_of_powerset_sum_eq`). The field $\mathbb F_2$ satisfies the required additive cancellation, so the conclusion follows.

**Key facts.** `FABL.coefficients_eq_of_powerset_sum_eq`.

**Caveat.** The supplied informal statement describes a different result; this account follows the formal statement and proof source.
