<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalBlockTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computation by the Canonical Block Tree

**Claim.** The canonical block tree computes the DNF after the initial restriction completes free coordinates from a Boolean input and fixes the other coordinates to their prescribed signs.

**Proof.** Use the pointwise characterisation of computation by a decision tree (`FABL.F₂DecisionTree.computes_iff`), so it suffices to evaluate the tree on an arbitrary Boolean input. The raw coordinate tree is well formed, and converting it to the indexed decision tree preserves its evaluation (`FABL.CoordinateDecisionTree.eval_toF₂DecisionTree`). The auxiliary evaluation theorem says that with fuel $n$, the raw tree’s value equals the DNF evaluated at the completion of the initial restriction using that input (`FABL.DNFFormula.eval_canonicalBlockTreeAux`). The restriction, formula, and raw-tree definitions then identify this value with the desired restricted Boolean function.

**Key facts.** `FABL.F₂DecisionTree.computes_iff`, `FABL.CoordinateDecisionTree.eval_toF₂DecisionTree`, `FABL.DNFFormula.eval_canonicalBlockTreeAux`.
