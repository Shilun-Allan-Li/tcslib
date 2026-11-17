<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPExamples.lean :: FABL.maxCutInstance_exists_incident_constraint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An Incident Constraint for Every Variable

**Claim.** In a maximum-cut instance, every variable is an endpoint of some constraint containing it in its scope.

**Proof.** By the instance's participation condition, the chosen variable belongs to the scope of some constraint in the instance. Write that constraint as a predicate together with its scope. In the maximum-cut template the predicate is the unique unit predicate and every scope has two positions, so the variable's preimage in the scope is either the first or the second position. Thus the variable equals one of the two endpoints of this constraint.
