<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.computes_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise characterization of computation

**Claim.** A decision tree computes a function if and only if its evaluation agrees with that function at every input.

**Proof.** By definition, computation means equality of the evaluation function and the target function. Function extensionality says that two functions are equal exactly when their values agree at every argument (`funext_iff`). Applying this characterization gives the stated equivalence.
