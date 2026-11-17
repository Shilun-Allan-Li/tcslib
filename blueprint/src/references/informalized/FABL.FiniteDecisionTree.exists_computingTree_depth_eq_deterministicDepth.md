<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.exists_computingTree_depth_eq_deterministicDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Tree Attaining Deterministic Depth

**Claim.** For a function on inputs from a finite nonempty alphabet, there is a decision tree computing it whose depth equals the deterministic depth.

**Proof.** The existence theorem for a computing tree with a specified depth gives a depth $d$ and a tree $T$ that computes $f$ and has depth $d$. By definition, the deterministic depth is the least natural number satisfying that existence property. The witness principle for this least number (`Nat.find_spec`) therefore supplies a computing tree whose depth is exactly the deterministic depth.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_with_depth`.
