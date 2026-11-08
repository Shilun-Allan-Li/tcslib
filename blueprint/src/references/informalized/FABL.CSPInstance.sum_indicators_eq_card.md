<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.sum_indicators_eq_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constraint Indicator Sum

**Claim.** For any multiset of constraints and any assignment, the sum of the satisfied indicators plus the sum of the unsatisfied indicators equals the multiset's cardinality.

**Proof.** Induct on the constraint multiset. For the empty multiset, both indicator sums and the cardinality are zero. For a multiset formed by adding a constraint $c$ to a smaller multiset, the two indicator sums each gain the corresponding indicator of $c$, and the cardinality increases by one. The indicators for $c$ add to one (`satisfiedIndicator_add_unsatisfiedIndicator`); combining this with the induction hypothesis gives the equality for the enlarged multiset.

**Key facts.** `FABL.CSPConstraint.satisfiedIndicator_add_unsatisfiedIndicator`.
