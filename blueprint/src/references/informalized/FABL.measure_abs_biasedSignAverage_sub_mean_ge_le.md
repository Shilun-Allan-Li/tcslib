<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.measure_abs_biasedSignAverage_sub_mean_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration of the Biased Sign Average

**Claim.** For $n>0$, $p\in[0,1]$, and $t\ge0$, the probability that the average of $n$ independent signs, each with mean $1-2p$, differs from $1-2p$ in absolute value by at least $t$ is at most $2\exp(-nt^2/2)$.

**Proof.** Represent the signs on the product probability space and center each coordinate by subtracting its mean $1-2p$. Each centered coordinate is sub-Gaussian with parameter $1$: it is bounded in an interval of length $2$, and its expectation is the prescribed mean. The product representation gives independence of these centered coordinates. The sub-Gaussian sum bound therefore controls the probability that their sum is at least $nt$ by $\exp(-(nt)^2/(2n))$. Apply the same bound to the negative of the sum for the lower tail. The event that the absolute centered average is at least $t$ is the union of these two tail events, so subadditivity gives the sum of their bounds. Simplifying the exponent yields $2\exp(-nt^2/2)$.

**Key facts.** `FABL.productProbabilityPMF_biasedSign_toMeasure_eq_pi`, `FABL.pmfExpectation_eq_integral`, `FABL.pmfExpectation_biasedSignPMF_signValue`.
