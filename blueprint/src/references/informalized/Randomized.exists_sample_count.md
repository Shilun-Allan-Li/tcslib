<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.exists_sample_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Sample Count for Bernoulli Averages

**Claim.** For positive $\varepsilon,\delta$ with $\delta\leq 1/2$, there is an integer $k_0\leq \log(1/\delta)/\varepsilon^2+1$ such that for every Bernoulli parameter $p$, every $k\geq k_0$, the probability that the sample average differs from $p$ by more than $\varepsilon$ is at most $\delta$.

**Proof.** Choose $k_0=\left\lceil\log(2/\delta)/(2\varepsilon^2)\right\rceil$. Since $\delta\leq1/2$, we have $\log 2\leq\log(1/\delta)$ and therefore $\log(2/\delta)\leq2\log(1/\delta)$. It follows that the real number inside the ceiling is at most $\log(1/\delta)/\varepsilon^2$; the ceiling is at most that bound plus one. For any $k\geq k_0$, the sample size meets the threshold in the Bernoulli average concentration theorem (`Randomized.iid_bernoulli_avg_concentration_of_le`). Applying that theorem gives the claimed probability bound.

**Key facts.** `Randomized.iid_bernoulli_avg_concentration_of_le`.
