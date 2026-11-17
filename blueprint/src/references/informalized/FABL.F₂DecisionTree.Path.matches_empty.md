<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.matches_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Every point matches the empty path

**Claim.** For any terminal label and any point of the binary cube, the empty path matches that point.

**Proof.** To check matching, take any coordinate and any proposed branch value. The empty path assigns `none` at every coordinate, so its assignment cannot equal `some` of that value. Hence there is no specified coordinate whose value could fail to agree, and the matching condition holds.
