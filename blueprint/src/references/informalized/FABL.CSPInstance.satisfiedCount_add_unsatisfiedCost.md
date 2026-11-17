<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.satisfiedCount_add_unsatisfiedCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfied Count and Unsatisfied Cost

**Claim.** For any instance and assignment, the satisfied count plus the total unsatisfied cost equals the number of constraints, with multiplicities counted.

**Proof.** First express the instance's unsatisfied cost as the sum, over its constraint multiset, of the unsatisfied indicators (`unsatisfiedCost_eq_sum`). For each constraint, its satisfied and unsatisfied indicators add to $1$ (`satisfiedIndicator_add_unsatisfiedIndicator`). Summing this identity across the multiset gives the constraint's cardinality on the right, while the two sums on the left are the satisfied count and the unsatisfied cost. This is the stated equality.

**Key facts.** `FABL.CSPInstance.unsatisfiedCost_eq_sum`, `FABL.CSPInstance.sum_indicators_eq_card`.
