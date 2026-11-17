<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.withQuery_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output under a coordinate query

**Claim.** Updating a path to fix a chosen coordinate to a chosen bit leaves its terminal label unchanged.

**Proof.** The update changes only the assignment component of the path. Its output component is defined to be the original path's output, so the two terminal labels are equal by the definition of the update.
