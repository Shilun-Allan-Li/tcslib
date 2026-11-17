<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.value_eq_one_iff_fullySatisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value One and Full Satisfaction

**Claim.** An instance has value one under an assignment exactly when every constraint in it is satisfied by that assignment.

**Proof.** The instance has at least one constraint, so its constraint count is nonzero. Rewrite its value as one minus the unsatisfied cost divided by that count. This equals one precisely when the quotient is zero; since the denominator is nonzero, this is equivalent to the unsatisfied cost being zero. The characterization of full satisfaction by zero unsatisfied cost (`FABL.CSPInstance.fullySatisfied_iff_unsatisfiedCost_eq_zero`) now gives both directions.

**Key facts.** `FABL.CSPInstance.value_eq_one_sub_unsatisfiedCost_div`, `FABL.CSPInstance.fullySatisfied_iff_unsatisfiedCost_eq_zero`.
