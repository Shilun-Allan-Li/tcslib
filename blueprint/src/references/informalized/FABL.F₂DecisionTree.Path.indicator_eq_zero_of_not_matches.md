<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.indicator_eq_zero_of_not_matches -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Outside a Path Cylinder

**Claim.** If a binary vector does not match a path, the indicator of the path’s cylinder at the vector is zero.

**Proof.** A vector that does not match the path is outside its cylinder, since the cylinder consists exactly of matching vectors. The indicator of a set is zero outside that set, giving the claimed value.
