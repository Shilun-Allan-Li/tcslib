<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.coordinateRestriction_surjective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Surjectivity of coordinate restriction

**Claim.** Restricting vectors in $\mathbb F_2^n$ to any selected set of coordinates gives a surjective linear map to the functions on that set.

**Proof.** Given any function on the selected coordinates, extend it to the whole cube by assigning its prescribed values on those coordinates and zero elsewhere. Restricting this extension recovers the original function at every selected coordinate. Thus every target function has a preimage, proving surjectivity.
