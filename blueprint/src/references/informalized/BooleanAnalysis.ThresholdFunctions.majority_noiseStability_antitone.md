<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.majority_noiseStability_antitone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Noise Stability Monotonicity

**Claim.** For $0\leq\rho\leq1$, the noise stability of majority on the cube of dimension $2(m+1)+1$ is at most that of majority on the cube of dimension $2m+1$.

**Proof.** Write the noise stability of each majority function as the sum of $\rho^k$ times its Fourier weight at level $k$, using the level-sum formula for noise stability (`noiseStability_eq_sum_weightLevel`). Both sums can be taken over levels below $2(m+1)+2$: the smaller cube's additional levels contribute zero, since Fourier weight vanishes above the dimension (`weightLevel_eq_zero_of_lt`).

The two majority functions have total Fourier weight $1$, by the total-weight identity for Boolean functions taking values in $\{\pm1\}$ (`sum_weightLevel_eq_one`, using `majority_isPmOne`). Their level weights also satisfy the required cumulative comparison: through every level in the common range, the larger majority's cumulative weight is at most the smaller one's (`majority_prefix_weight_le`). The summation-by-parts comparison for weights with ordered cumulative sums, applied with the decreasing sequence $\rho^k$ for $0\leq\rho\leq1$, now gives the claimed inequality (`sum_pow_mul_le_of_prefix_le`).

**Key facts.** `BooleanAnalysis.ThresholdFunctions.weightLevel_eq_zero_of_lt`, `BooleanAnalysis.ThresholdFunctions.noiseStability_eq_sum_weightLevel`, `BooleanAnalysis.ThresholdFunctions.majority_isPmOne`, `BooleanAnalysis.ThresholdFunctions.sum_weightLevel_eq_one`, `BooleanAnalysis.ThresholdFunctions.majority_prefix_weight_le`, `BooleanAnalysis.ThresholdFunctions.sum_pow_mul_le_of_prefix_le`.
