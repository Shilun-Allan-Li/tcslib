<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.maximumProductInfluence_ge_variance_div_deterministicDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance versus deterministic depth

**Claim.** Under the stated full-support and orthonormal-basis assumptions, a nonconstant sign-valued function has variance divided by deterministic decision-tree depth at most its maximum coordinate influence.

**Proof.** Choose a deterministic tree computing the function whose depth is its deterministic decision-tree depth. Regard it as a randomized tree with a single deterministic choice. The randomized variance bound controls the variance by maximum influence times its average cost. The average cost is at most the worst-case cost, and the deterministic tree's worst-case cost is at most its depth. Since maximum influence is nonnegative, these comparisons yield $V\le M\,d$, where $V$ is the variance, $M$ the maximum influence, and $d$ the deterministic depth. Full support and nonconstancy imply $V>0$, so $d$ cannot be zero in this inequality; thus $d>0$. Dividing by $d$ proves the result.

**Key facts.** `FABL.FiniteDecisionTree.exists_computingTree_depth_eq_deterministicDepth`, `FABL.RandomizedDecisionTree.variance_le_maxInfluence_mul_averageCost`, `FABL.RandomizedDecisionTree.averageCost_le_worstCaseCost`, `FABL.RandomizedDecisionTree.worstCaseCost_ofDeterministic_le_depth`, `FABL.maximumProductInfluence_nonneg`, `FABL.productVariance_pos_of_nonconstant`.
