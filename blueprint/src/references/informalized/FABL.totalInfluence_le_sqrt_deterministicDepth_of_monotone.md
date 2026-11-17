<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.totalInfluence_le_sqrt_deterministicDepth_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound from Decision Tree Depth

**Claim.** If a monotone Boolean function has a deterministic decision tree computing its real-valued sign representation with deterministic depth at most $k$, then that representation has total influence at most $\sqrt{k}$.

**Proof.** Choose a deterministic tree computing the real-valued representation whose depth is the deterministic depth of the function. Regard it as a randomized decision tree that makes no random choices. Apply the monotone-function influence bound for randomized decision trees, which bounds product total influence by the bias scale times the square root of average cost (`FABL.RandomizedDecisionTree.totalInfluence_le_sigma_mul_sqrt_averageCost`). Set the bias parameter to $1/2$: its biased sign law is the uniform law (`FABL.biasedSignPMF_one_half_eq_uniform`), and its bias scale is $1$. Thus product total influence under the uniform law is the ordinary total influence (`FABL.productTotalInfluence_uniformSign_eq_totalInfluence`), and the bound reduces to the square root of the tree's average cost. The average cost is at most its worst-case cost (`FABL.RandomizedDecisionTree.averageCost_le_worstCaseCost`), and for a deterministic tree that cost is at most the tree depth (`FABL.RandomizedDecisionTree.worstCaseCost_ofDeterministic_le_depth`). The chosen depth equals the deterministic depth, which is at most $k$. Monotonicity of the square root now gives the claimed bound.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_depth_eq_deterministicDepth`, `FABL.RandomizedDecisionTree.totalInfluence_le_sigma_mul_sqrt_averageCost`, `FABL.biasedSignPMF_one_half_eq_uniform`, `FABL.productTotalInfluence_uniformSign_eq_totalInfluence`, `FABL.RandomizedDecisionTree.averageCost_le_worstCaseCost`, `FABL.RandomizedDecisionTree.worstCaseCost_ofDeterministic_le_depth`.
