<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/LinearCSPAlgorithms.lean :: FABL.CSPConstraint.isSatisfied_toF₂LinearEquation_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalence of Constraint and Equation Satisfaction

**Claim.** For every assignment, the associated linear equation is satisfied exactly when the constraint is satisfied.

**Proof.** The associated equation evaluates to the sum of the assigned values along the constraint’s scope (`FABL.CSPConstraint.eval_toF₂LinearEquation`). Its constant is the predicate’s right-hand side, so equation satisfaction says that this sum equals that right-hand side. By the maximum-arity linear template’s definition, the constraint’s Boolean evaluation is precisely the decision of the same equality. A Boolean decision is true exactly when the proposition it decides holds, proving the equivalence.

**Key facts.** `FABL.CSPConstraint.eval_toF₂LinearEquation`.
