<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.exists_computingTree_with_leafCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a Computing Tree with Finite Leaf Count

**Claim.** For a finite nonempty alphabet, every function on length-$n$ inputs has a decision tree that computes it and has some natural-number leaf count.

**Proof.** Take the complete tree for $f$. The completeness theorem says that this tree computes $f$. Choose its leaf count as the natural number $s$; by definition, the tree has leaf count $s$. These choices give the required witnesses.

**Key facts.** `FABL.FiniteDecisionTree.completeTree_computes`.
