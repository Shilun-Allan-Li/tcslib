<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.value_eq_one_sub_unsatisfiedCost_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value from Unsatisfied Cost

**Claim.** For any constraint satisfaction instance and assignment, the fraction of satisfied constraints equals one minus the total unsatisfied cost divided by the number of constraints.

**Proof.** The constraint count is nonzero because the multiset of constraints is nonempty. The satisfied count plus the unsatisfied cost equals the constraint count (`FABL.CSPInstance.satisfiedCount_add_unsatisfiedCost`). Divide this identity by the constraint count and rearrange: the satisfied count divided by the constraint count is one minus the unsatisfied cost divided by that count. By definition, the first quotient is the value.

**Key facts.** `FABL.CSPInstance.satisfiedCount_add_unsatisfiedCost`.
