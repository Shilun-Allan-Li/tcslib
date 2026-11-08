<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.queryProbability_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative query probability

**Claim.** For every coordinate $i$, the probability that $T$ queries $i$ under independent inputs of law $\pi$ is nonnegative.

**Proof.** Fix an input. For every seed, the indicator of whether the selected tree queries $i$ is either $0$ or $1$, hence nonnegative. Nonnegativity of expectation ($\texttt{FABL.pmfExpectation\_nonneg}$) shows that the query probability for this input is nonnegative. Applying the same fact to the expectation over inputs proves the claim.

**Key facts.** `FABL.pmfExpectation_nonneg`.
