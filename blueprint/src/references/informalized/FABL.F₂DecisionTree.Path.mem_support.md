<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.mem_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the path support

**Claim.** A coordinate belongs to the path's support exactly when its path assignment is defined.

**Proof.** The support is the set of coordinates whose assignment is not `none`. Therefore membership in the support is equivalent, by the definition of filtered support, to the assignment being different from `none`.
