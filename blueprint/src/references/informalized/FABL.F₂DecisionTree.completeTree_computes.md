<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.completeTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the constructed tree

**Claim.** The recursively constructed complete decision tree for $f$ computes $f$ on every input of the binary cube.

**Proof.** The evaluation theorem for the recursively constructed complete tree states that its evaluation is exactly $f$ (`FABL.F₂DecisionTree.eval_completeTree`). By the definition of computing a function, this equality says that the complete tree computes $f$.

**Key facts.** `FABL.F₂DecisionTree.eval_completeTree`.
