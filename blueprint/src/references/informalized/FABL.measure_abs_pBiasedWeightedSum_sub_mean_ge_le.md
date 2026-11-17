<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.measure_abs_pBiasedWeightedSum_sub_mean_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration of a Weighted Bernoulli Sum

**Claim.** For independent Bernoulli-valued choices $f(x)$ with probability $p$ of value $1$, any real weights $w(x)$, and $t\ge0$, the probability that $\left|\sum_x w(x)(f(x)-p)\right|\ge t$ is at most $2\exp\!\left(-t^2/(2\sum_x w(x)^2)\right)$.

**Proof.** Use the product measure representing the independent choices, as supplied by the product-measure identification ($\texttt{FABL.pBiasedRandomFunctionPMF_toMeasure}$). For each point $x$ of the cube, the variable $f\mapsto f(x)$ lies in $[0,1]$, and its expectation is $p$, given by the one-coordinate expectation identity ($\texttt{FABL.integral_zeroOneValue_pBiasedBitPMF}$). The bounded-variable sub-Gaussian inequality then gives parameter $1$ for $f(x)-p$. Multiplication by $w(x)$ changes that parameter to $w(x)^2$. The coordinate variables are independent under the product measure, so the sub-Gaussian sum inequality gives parameter $\sum_x w(x)^2$ for their weighted sum. Apply its upper-tail bound both to the sum and its negative. The event that the absolute value is at least $t$ is the union of those tails; adding their bounds gives the stated estimate.

**Key facts.** `FABL.pBiasedRandomFunctionPMF_toMeasure`, `FABL.integral_zeroOneValue_pBiasedBitPMF`.
