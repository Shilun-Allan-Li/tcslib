<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.codimension_coordinateZeroSubspace_eq_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Codimension of a Path Support

**Claim.** The codimension of the subspace of binary vectors vanishing on the coordinates fixed by a path equals the path’s length.

**Proof.** Apply the fact that the codimension of the coordinate-zero subspace on a finite set of coordinates equals the cardinality of that set (`FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace`). The path’s length is defined to be the cardinality of its support, so the two quantities agree.

**Key facts.** `FABL.F₂DecisionTree.f₂Codimension_coordinateZeroSubspace`.
