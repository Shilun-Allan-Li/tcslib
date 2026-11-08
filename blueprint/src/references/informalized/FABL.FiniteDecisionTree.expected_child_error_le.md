<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.expected_child_error_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Child Error Bound

**Claim.** The average error of the child trees is at most the error of the tree that first queries coordinate $i$, plus half the product influence at $i$.

**Proof.** Let $P$ be the tree that queries $i$ and then uses the prescribed child. First, for each alphabet symbol $\omega$ and input $x$, the child indexed by $\omega$ has the same evaluation on $x$ as $P$ has on the input obtained by replacing $x_i$ with $\omega$. Indeed, the child has no access to coordinate $i$, so its evaluation is unchanged by that replacement (`eval_eq_of_agreeOn`); after replacement, the root query selects exactly that child.

Apply this identity to express the child error as the error of $P$ on the resampled input, while comparing it with $f$ at the original input. The disagreement indicator obeys the triangle inequality: disagreement between the tree's prediction and $f(x)$ is bounded by the sum of disagreement between the prediction and the resampled value of $f$, and disagreement between the two values of $f$ (`disagreementIndicator_triangle`). Averaging this pointwise inequality over the input and the resampled coordinate preserves the inequality (`pmfExpectation_mono`).

The average of the first term is exactly the error probability of $P$: resampling coordinate $i$ leaves the product distribution unchanged, by the identity for averaging a product mean after fixing a coordinate (`pmfExpectation_productMean_fixProductCoordinate`). The average of the second term is the probability that resampling coordinate $i$ changes $f$. To put it in that form, interchange the two finite expectations (`pmfExpectation_comm`) and use symmetry of disagreement. Linearity of expectation separates these two contributions (`pmfExpectation_add_fun`). Finally, the basis identity says that the product influence at $i$ is twice this resampling-disagreement probability (`FiniteFourierBasis.productInfluence_eq_two_mul_resamplingDisagreement`). Substitution gives the claimed error bound.

**Key facts.** `FABL.FiniteDecisionTree.eval_eq_of_agreeOn`, `FABL.disagreementIndicator_triangle`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_productMean_fixProductCoordinate`, `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_comm`, `FABL.FiniteFourierBasis.productInfluence_eq_two_mul_resamplingDisagreement`.
