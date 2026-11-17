<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.totalInfluence_le_sqrt_logb_deterministicSize_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound from Minimum Tree Size

**Claim.** For a monotone Boolean function, total influence is at most the square root of the base-two logarithm of the minimum number of leaves in a deterministic decision tree computing it.

**Proof.** Choose a deterministic decision tree computing the target whose leaf count equals its deterministic size (`FABL.FiniteDecisionTree.exists_computingTree_leafCount_eq_deterministicSize`). Apply the bound for a monotone Boolean function computed by a tree: its total influence is at most the square root of the base-two logarithm of that tree's leaf count (`FABL.totalInfluence_le_sqrt_logb_leafCount_of_monotone`). Substituting the chosen tree's leaf count by the deterministic size gives the result.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_leafCount_eq_deterministicSize`, `FABL.totalInfluence_le_sqrt_logb_leafCount_of_monotone`.
