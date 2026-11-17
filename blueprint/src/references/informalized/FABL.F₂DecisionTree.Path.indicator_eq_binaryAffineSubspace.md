<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.indicator_eq_binaryAffineSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator of the Path Affine Subspace

**Claim.** The indicator of a path’s cylinder equals the indicator of the translate, by its base vector, of the subspace of vectors vanishing on the path’s support.

**Proof.** By definition, the path indicator is the indicator function of its cylinder. The cylinder equals the stated affine subspace (`FABL.F₂DecisionTree.Path.cylinder_eq_binaryAffineSubspace`), so their indicator functions agree.

**Key facts.** `FABL.F₂DecisionTree.Path.cylinder_eq_binaryAffineSubspace`.
