<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.sum_shapleyValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Shapley Values

**Claim.** For a real-valued function on the subsets of $\{1,\ldots,n\}$, the sum of its Shapley values is its value on the full set minus its value on the empty set.

**Proof.** Expand each Shapley value linearly in the point indicators of subsets: the Shapley value of $f$ is the sum, over subsets $A$, of $f(A)$ times the Shapley value of the indicator of $A$ (`shapleyValue_eq_sum_pointIndicators`). Interchange the two finite sums and factor $f(A)$ out of the inner sum. The sum of the point-indicator Shapley values over coordinates is first identified with its layer-weight expression (`sum_shapleyValue_subsetPointIndicator_eq_layerExpression`), and that expression simplifies to $1$ when $A$ is the full set, $-1$ when $A$ is empty, and $0$ otherwise (`shapleyLayerExpression_eq_endpointIndicators`). Consequently only the endpoint terms remain, giving $f(\{1,\ldots,n\})-f(\varnothing)$.

**Key facts.** `FABL.shapleyValue_eq_sum_pointIndicators`, `FABL.sum_shapleyValue_subsetPointIndicator_eq_layerExpression`, `FABL.shapleyLayerExpression_eq_endpointIndicators`.
