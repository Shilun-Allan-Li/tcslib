<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.productMean_biasedQueryScore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Biased Query Score

**Claim.** For a decision tree on sign inputs, the mean of the sum of standardized signs on its queried coordinates is zero under the product distribution with negative-sign probability $p$, for $0<p<1$.

**Proof.** Induct on the tree. At a leaf the query score is identically zero, so its mean is zero. At a query of coordinate $j$, the score is the standardized sign at $j$ plus the score of the child selected by the observed sign (`biasedQueryScore_query`). The child score ignores coordinate $j$, because $j$ is no longer available (`biasedQueryScore_replaceCoordinate_of_not_mem`). Thus the product mean of the score that follows the query can be evaluated by first fixing the value $\omega$ at $j$ and averaging over the remaining coordinates (`productMean_diagonal_section`). For each fixed $\omega$, the mean of the child's score is zero by induction; adding the constant standardized sign at $\omega$ leaves just that constant in the conditional mean. Averaging over $\omega$ gives the mean of a single standardized sign, which is zero (`pmfExpectation_biasedStandardizedSign`).

**Key facts.** `FABL.FiniteDecisionTree.biasedQueryScore_query`, `FABL.FiniteDecisionTree.biasedQueryScore_replaceCoordinate_of_not_mem`, `FABL.FiniteDecisionTree.productMean_diagonal_section`, `FABL.pmfExpectation_biasedStandardizedSign`.
