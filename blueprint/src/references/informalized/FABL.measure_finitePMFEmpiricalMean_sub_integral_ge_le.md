<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SparsePolynomialApproximation.lean :: FABL.measure_finitePMFEmpiricalMean_sub_integral_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-law empirical concentration

**Claim.** For independent samples from a finite law, the probability that the empirical mean of a function valued in $[-1,1]$ differs from its expectation by at least $\varepsilon$ is at most $2\exp(-m\varepsilon^2/2)$.

**Proof.** The product law of the samples is the product measure with one-coordinate law $p$ (`independentProductPMF_toMeasure`). Write $\mu=\int g\,dp$ and center each coordinate by $\mu$. Each centered coordinate has sub-Gaussian moment generating function with parameter $1$, because a random variable in $[-1,1]$ has this centered bound. The coordinates are independent under the product measure. The independent-sum sub-Gaussian tail bound therefore gives probability at most $\exp(-((m\varepsilon)^2)/(2m))$ for the centered sum to be at least $m\varepsilon$; applying the same bound to its negative gives the same estimate for the lower tail. The empirical-mean error is the centered sum divided by $m$, so its absolute-deviation event is the union of these two tail events. By the union bound its probability is at most twice the one-sided estimate. Since $m>0$, the exponent simplifies to $-m\varepsilon^2/2$.

**Key facts.** `FABL.independentProductPMF_toMeasure`.
