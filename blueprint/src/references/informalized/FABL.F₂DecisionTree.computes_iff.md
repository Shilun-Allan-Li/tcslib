<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.computes_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise characterization of computation

**Claim.** A decision tree computes a function exactly when its evaluation agrees with that function at every input.

**Proof.** By definition, computation means equality of the tree's evaluation function and the target function. Equality of functions is equivalent to equality at every input, giving the stated characterization.
