<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPConstraint.evalSolution_toValuedTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constraint Cost on an Assignment

**Claim.** For any assignment, the associated valued term has cost zero when the constraint is satisfied and cost one when it is not.

**Proof.** Evaluate the valued term on the assignment. By the definitions of the valued term’s solution cost and the template’s unsatisfied cost, this is the indicator that the predicate evaluation is false. The constraint’s unsatisfied indicator is defined by that same Boolean case distinction, so the two values agree.
