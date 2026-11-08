<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.iid_bernoulli_avg_concentration -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernoulli Average Concentration

**Claim.** For $p\in[0,1]$ and $k>0$, under the product distribution of $k$ independent Bernoulli-$p$ bits, the probability that the fraction of successes differs from $p$ by more than $\delta>0$ is at most $2\exp(-2\delta^2k)$.

**Proof.** First split the event of absolute deviation into its upper and lower cases. Summing the coordinatewise differences between each indicator and $p$ gives the success count minus $kp$; summing the opposite differences gives $kp$ minus the success count. Thus the upper-deviation event is contained in the event that the first sum is at least $\delta k$, and the lower-deviation event is contained in the analogous event for the opposite differences.

The coordinate indicators are mutually independent by the product-measure independence result (`Randomized.iIndepFun_coordIndicator`). Applying the same measurable transformation separately to each coordinate preserves independence, so both centered families are independent. Each has sub-Gaussian parameter $(1/2)^2$ by the coordinate bounds (`Randomized.hasSubgaussianMGF_coordIndicator_sub` and `Randomized.hasSubgaussianMGF_sub_coordIndicator`). The independent-sum tail inequality therefore bounds each one-sided event by $\exp(-2\delta^2k)$. By the union bound, the two-sided event has probability at most the sum of these bounds, namely $2\exp(-2\delta^2k)$.

**Key facts.** `Randomized.iIndepFun_coordIndicator`, `Randomized.hasSubgaussianMGF_coordIndicator_sub`, `Randomized.hasSubgaussianMGF_sub_coordIndicator`, `Randomized.iidBernoulli_tail_le`.
