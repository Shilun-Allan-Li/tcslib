<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/SparseSampling.lean :: BooleanAnalysis.ThresholdFunctions.sample_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-sided sample tail bound

**Claim.** For independent, measurable random variables $Y_i$ taking values in $[-1,1]$ almost surely and all having mean $m$, the probability that their sum exceeds its mean by at least $s\varepsilon$ is at most $\exp(-s\varepsilon^2/2)$, for $s>0$ and $\varepsilon\ge0$.

**Proof.** Center each variable by setting $X_i=Y_i-\int Y_i\,d\mu$. Independence is preserved under applying a measurable function separately to each variable. The bounded-variable subgaussian estimate says that a variable in an interval of length $2$ has centered subgaussian parameter $1$; hence each $X_i$ has that bound. The independent-sum subgaussian tail inequality then bounds the probability that $\sum_i X_i$ is at least $s\varepsilon$ by the exponential of minus the squared threshold divided by twice the sum of the parameters. Here the sum of the parameters is $s$, so the bound is $\exp(-(s\varepsilon)^2/(2s))=\exp(-s\varepsilon^2/2)$. Finally, the common-mean assumption identifies $\sum_i X_i$ with $\sum_iY_i-sm$, giving the stated event and estimate.
