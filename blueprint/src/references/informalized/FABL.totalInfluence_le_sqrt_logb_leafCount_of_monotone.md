<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.totalInfluence_le_sqrt_logb_leafCount_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound from Leaf Count

**Claim.** For a monotone Boolean function computed by a deterministic decision tree, its total influence is at most the square root of the base-two logarithm of the tree's leaf count.

**Proof.** Map the output labels of the given tree through the sign-to-real map. The resulting tree computes the real-valued sign representation (`FABL.FiniteDecisionTree.mapOutput_signValue_computes`), and this change of labels preserves the number of leaves (`FABL.FiniteDecisionTree.leafCount_mapOutput`). Regard this real-output tree as a randomized decision tree making no random choices. At bias parameter $1/2$, the biased law is uniform (`FABL.biasedSignPMF_one_half_eq_uniform`) and the bias scale is $1$. The monotone-function randomized-tree influence bound therefore bounds total influence by the square root of the tree's average cost, using the equality between uniform product total influence and ordinary total influence (`FABL.productTotalInfluence_uniformSign_eq_totalInfluence`). The average cost of this deterministic tree equals its deterministic average cost (`FABL.RandomizedDecisionTree.averageCost_ofDeterministic`), and that deterministic average cost is at most the base-two logarithm of its leaf count (`FABL.FiniteDecisionTree.deterministicAverageCost_le_log_leafCount`). Taking square roots preserves this inequality and proves the claim.

**Key facts.** `FABL.FiniteDecisionTree.mapOutput_signValue_computes`, `FABL.RandomizedDecisionTree.totalInfluence_le_sigma_mul_sqrt_averageCost`, `FABL.biasedSignPMF_one_half_eq_uniform`, `FABL.productTotalInfluence_uniformSign_eq_totalInfluence`, `FABL.RandomizedDecisionTree.averageCost_ofDeterministic`, `FABL.FiniteDecisionTree.deterministicAverageCost_le_log_leafCount`, `FABL.FiniteDecisionTree.leafCount_mapOutput`.

**Caveat.** The supplied informal statement describes unrelated inequalities; the account follows the formal statement and proof source.
