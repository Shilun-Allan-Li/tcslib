<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productTotalInfluence_ge_variance_div_functionRevealment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance and revealment bound

**Claim.** For a nonconstant sign-valued function on a finite product space with full-support coordinate law, its variance divided by its function revealment is at most its total influence.

**Proof.** Write $V$ for the variance and $I$ for the total influence. First, full support and nonconstancy imply $V>0$ (the variance vanishes only when the function is constant on every input). The Fourier-basis variance bound gives $V\le I$, hence $I>0$. For any randomized decision tree $T$ computing the function, the variance–revealment inequality gives $V\le \operatorname{revealment}(T) I$. Dividing by $I>0$ shows that $V/I$ is a lower bound for the revealment of every such tree. There is at least one computing tree: the complete deterministic tree, which queries coordinates until it can return the function value. Thus the set of tree revealments is nonempty, and its infimum, the function revealment, is at least $V/I>0$. Finally, from $V/I\le\operatorname{functionRevealment}$ and positivity of both denominators, rearranging yields $V/\operatorname{functionRevealment}\le I$.

**Key facts.** `FABL.productVariance_pos_of_nonconstant`, `FABL.FiniteFourierBasis.productVariance_le_productTotalInfluence`, `FABL.RandomizedDecisionTree.variance_le_revealment_mul_totalInfluence`, `FABL.FiniteDecisionTree.completeTree_computes`.
