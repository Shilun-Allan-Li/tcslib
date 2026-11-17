<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.sum_structuralQueryProbability_eq_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structural Probability Equals Average Cost

**Claim.** Under the stated finite orthonormal-basis assumptions, the sum of a tree's structural query probabilities over coordinates equals its expected query count for independent inputs with common law $\pi$.

**Proof.** For each coordinate, replace its structural query probability by its deterministic query probability, using the basis-dependent identity `deterministicQueryProbability_eq_structural`. The deterministic average cost and these probabilities are expectations over the independent product input law. By linearity of expectation (`pmfExpectation_sum`), the sum of the coordinate-wise expected query indicators is the expectation of their pointwise sum. On every input, that sum equals the query count by `sum_queryIndicator_eq_queryCount`. Taking expectations gives the asserted equality.

**Key facts.** `FABL.FiniteDecisionTree.deterministicQueryProbability_eq_structural`, `FABL.pmfExpectation_sum`, `FABL.FiniteDecisionTree.sum_queryIndicator_eq_queryCount`.
