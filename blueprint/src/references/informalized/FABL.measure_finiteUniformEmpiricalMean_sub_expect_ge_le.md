<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform empirical concentration

**Claim.** For independent uniform samples from a finite nonempty set, the probability that the empirical mean of a function valued in $[-1,1]$ differs from its uniform expectation by at least $\varepsilon$ is at most $2\exp(-m\varepsilon^2/2)$.

**Proof.** The uniform law on the space of $m$-tuples is the product of the uniform laws on the individual coordinates (`uniformSample_toMeasure_eq_pi`). Let $\mu$ be the uniform expectation of the observation; integration of any coordinate observation under the product law equals $\mu$ (`integral_uniformPMF_eq_expect`). Center each coordinate by $\mu$. Each centered coordinate is sub-Gaussian with parameter $1$, since the observation lies in $[-1,1]$, and the coordinates are independent under the product measure. The independent-sum sub-Gaussian tail estimate bounds each of the upper and lower tails of the centered sum, at threshold $m\varepsilon$, by $\exp(-((m\varepsilon)^2)/(2m))$. The empirical-mean error is that sum divided by $m$, so its absolute-deviation event is the union of those tails. The union bound gives twice the one-sided estimate, and simplifying the exponent using $m>0$ yields $2\exp(-m\varepsilon^2/2)$.

**Key facts.** `FABL.uniformSample_toMeasure_eq_pi`, `FABL.integral_uniformPMF_eq_expect`.
