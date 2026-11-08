<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.eval_toF₂DecisionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Is Preserved Under Conversion

**Claim.** Converting a coordinate decision tree that is well formed with respect to an available coordinate set preserves its evaluation at every Boolean-cube input.

**Proof.** Fix an input and induct on the tree. A leaf has the same stored value before and after conversion. At a query, the converted tree queries the same coordinate and has the converted zero and one children. Thus both evaluations choose the same branch, according to the value of that coordinate at the fixed input. The induction hypotheses identify the evaluation of each converted child with its original child, so the selected branch values agree.
