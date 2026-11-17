<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.iid_bernoulli_avg_concentration_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernoulli Average Concentration Threshold

**Claim.** For $p\in[0,1]$, $\varepsilon>0$, and $0<\delta\le1$, if $k\ge \log(2/\delta)/(2\varepsilon^2)$, then the probability that the fraction of successes differs from $p$ by more than $\varepsilon$ is at most $\delta$.

**Proof.** The lower bound on $k$ is positive, since $2/\delta>1$ and $\varepsilon>0$; hence $k>0$. Apply the two-sided Bernoulli average concentration bound (`Randomized.iid_bernoulli_avg_concentration`) with deviation $\varepsilon$. The assumed threshold rearranges to $\log(2/\delta)\le 2\varepsilon^2k$. Since the exponential function is increasing, this gives $\exp(-2\varepsilon^2k)\le \exp(-\log(2/\delta))=\delta/2$. Multiplying by $2$ bounds the probability by $\delta$.

**Key facts.** `Randomized.iid_bernoulli_avg_concentration`.
