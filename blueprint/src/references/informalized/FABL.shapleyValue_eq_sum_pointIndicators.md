<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_eq_sum_pointIndicators -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expansion by point indicators

**Claim.** For a real-valued function on the subsets of an $n$-element set, its Shapley value at a player is the sum over all subsets $A$ of $f(A)$ times the Shapley value of the indicator of the singleton collection containing $A$.

**Proof.** Decompose $f$ as the sum, over all subsets $A$, of the function that is $f(A)$ at $A$ and zero elsewhere. By additivity of the Shapley value (`shapleyValue_sum`), the Shapley value of this sum is the sum of the Shapley values of its terms. Homogeneity (`shapleyValue_smul`) pulls the scalar $f(A)$ out of each term, giving the claimed formula.

**Key facts.** `FABL.subsetPointIndicator_decomposition`, `FABL.shapleyValue_sum`, `FABL.shapleyValue_smul`.
