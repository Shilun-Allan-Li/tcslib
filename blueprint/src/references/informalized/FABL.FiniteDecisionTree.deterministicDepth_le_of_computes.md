<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.deterministicDepth_le_of_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimal deterministic depth bound

**Claim.** The minimum depth of a finite decision tree computing a given function is at most the depth of any particular finite decision tree that computes it.

**Proof.** The existence theorem supplies a computing tree whose depth realizes the set of possible computing-tree depths (FiniteDecisionTree.exists_computingTree_with_depth). By definition, deterministic depth is the least depth in this nonempty set. Since $T$ computes the function and has depth $T.depth$, that depth belongs to the set. The least element is therefore at most $T$’s depth.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_with_depth`.
