<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.sum_shapleyValue_subsetPointIndicator_eq_layerExpression -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Point Indicator Shapley Sum

**Claim.** For the indicator of a fixed subset $A$, the sum of its Shapley values over coordinates is $|A|(w_n(|A|)+w_n(|A|-1))-(n-|A|)(w_n(|A|)+w_n(|A|+1))$, with natural-number subtraction truncated at zero.

**Proof.** For each coordinate, the Shapley value of the indicator of $A$ is positive when the coordinate lies in $A$ and negative when it does not (`shapleyValue_subsetPointIndicator`). If $i\in A$, its value is the sum of the probabilities of sampling $A$ and $A\setminus\{i\}$. These probabilities are the corresponding layer weights (`shapleySubsetPMF_apply_toReal_eq_layerWeight`), and the latter set has size $|A|-1$. Summing over the $|A|$ coordinates in $A$ gives the first term. If $i\notin A$, the value is minus the sum of the probabilities of sampling $A$ and $A\cup\{i\}$, whose sizes are $|A|$ and $|A|+1$. There are $n-|A|$ such coordinates, giving the second, negative term. Combining the two sums yields the formula.

**Key facts.** `FABL.shapleyValue_subsetPointIndicator`, `FABL.shapleySubsetPMF_apply_toReal_eq_layerWeight`.
