<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.value_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on the Satisfied Fraction

**Claim.** For any constraint satisfaction instance and assignment, the fraction of satisfied constraints is at most one.

**Proof.** Express the value as one minus the unsatisfied cost divided by the constraint count (`FABL.CSPInstance.value_eq_one_sub_unsatisfiedCost_div`). Both the unsatisfied cost and the constraint count are nonnegative, and the count is positive, so their quotient is nonnegative. Subtracting a nonnegative number from one cannot increase the result above one.

**Key facts.** `FABL.CSPInstance.value_eq_one_sub_unsatisfiedCost_div`.
