<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/LinearCSPAlgorithms.lean :: FABL.CSPInstance.satisfiesRows_linearRows_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Rows and Constraint Satisfaction

**Claim.** For an assignment to the variables, every equation in the row list obtained from the linear constraints is satisfied if and only if every constraint in the instance is satisfied.

**Proof.** Suppose every row is satisfied. Given a constraint in the instance, its associated linear equation appears in the row list: the constraint belongs to the constraint multiset, hence to its list conversion, and mapping that list by the row construction produces its equation. The equivalence between satisfaction of a constraint and satisfaction of its associated equation (`isSatisfied_toF₂LinearEquation_iff`) then shows that this constraint is satisfied.

Conversely, suppose every constraint in the instance is satisfied. Any row in the constructed list is, by the definition of that list as a map, the equation associated to some constraint in the multiset. That constraint is satisfied by assumption, so the same equivalence shows that the row is satisfied. Both implications establish the claim.

**Key facts.** `FABL.CSPConstraint.isSatisfied_toF₂LinearEquation_iff`.
