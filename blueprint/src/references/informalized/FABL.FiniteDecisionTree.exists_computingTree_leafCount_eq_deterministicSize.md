<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.FiniteDecisionTree.exists_computingTree_leafCount_eq_deterministicSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Tree Attaining Deterministic Size

**Claim.** For a Boolean function on the sign cube, there is a decision tree computing it whose leaf count equals its deterministic size.

**Proof.** The existence theorem for a computing tree with a specified leaf count provides a size and a tree computing the target with that leaf count. Deterministic size is defined as the least natural number for which such a tree exists. Applying the least-number witness principle (`Nat.find_spec`) to that existence theorem yields a computing tree whose leaf count is exactly the deterministic size.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_with_leafCount`.
