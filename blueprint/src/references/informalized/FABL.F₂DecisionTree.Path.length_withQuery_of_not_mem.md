<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.length_withQuery_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path length after a new query

**Claim.** Adding a coordinate not already specified by the path increases the number of specified coordinates by one.

**Proof.** The support after adding the query is the old support with the new coordinate inserted (`support_withQuery`). Since the coordinate was not in the old support, insertion increases the support's cardinality by one. Path length is the cardinality of the support, so the new length is the old length plus one.

**Key facts.** `FABL.F₂DecisionTree.Path.support_withQuery`.
