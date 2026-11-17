<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.forall_satisfied_iff_sum_unsatisfied_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction and zero unsatisfied count

**Claim.** Every constraint in a multiset is satisfied by an assignment if and only if the sum of its unsatisfied indicators, counted with multiplicity, is zero.

**Proof.** Induct on the constraint multiset. For the empty multiset, the universal satisfaction condition holds vacuously and the sum is zero. For a multiset formed by adding one constraint to a remainder, every constraint is satisfied exactly when the added constraint and every constraint in the remainder are satisfied. The sum of unsatisfied indicators is the added indicator plus the remainder’s sum; since both are natural numbers, it is zero exactly when each is zero. The added indicator is zero exactly when its Boolean evaluation is true, which is precisely satisfaction. The induction hypothesis handles the remainder.
