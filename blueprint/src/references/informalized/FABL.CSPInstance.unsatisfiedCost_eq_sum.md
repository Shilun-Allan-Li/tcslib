<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.unsatisfiedCost_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unsatisfied Cost as an Indicator Sum

**Claim.** For any constraint satisfaction instance and assignment, the total unsatisfied cost is the sum of the unsatisfaction indicators over the constraints, with multiplicities counted.

**Proof.** Expand the total cost as the evaluation of the associated valued constraint instance, and expand that evaluation as a sum over the multiset of constraints. Each constraint is mapped to the valued term given by its predicate, arity, and scope. Evaluating that term on the assignment evaluates the predicate on the assigned values in its scope, so its cost is exactly the indicator that the constraint is unsatisfied. Mapping constraints to terms and then evaluating therefore gives the same multiset of summands as mapping them directly to their unsatisfaction indicators. Their sums agree, including multiplicities.
