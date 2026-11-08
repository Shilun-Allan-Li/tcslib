<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.measure_abs_weightedBooleanSum_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration of a Weighted Boolean Sum

**Claim.** For a uniformly random Boolean-valued sign function $f$ on the cube and real weights $w(a)$, the probability that $\left|\sum_a w(a)f(a)\right|\ge t$ is at most $2\exp\!\left(-t^2/(2\sum_a w(a)^2)\right)$ for every $t\ge0$.

**Proof.** The uniform law on sign functions is the product of uniform laws on individual signs, by the product-measure identification ($\texttt{FABL.uniformBooleanFunction_toMeasure_eq_pi}$). Each coordinate sign takes only the values $-1$ and $1$ ($\texttt{FABL.signValue_eq_neg_one_or_one}$), and its expectation under the uniform law is zero ($\texttt{FABL.integral_signValue_uniformPMF}$). The bounded, mean-zero sub-Gaussian inequality therefore gives parameter $1$ for each coordinate. Multiplication by $w(a)$ gives parameter $w(a)^2$; independence then yields parameter $\sum_a w(a)^2$ for the weighted sum. The sub-Gaussian upper-tail bound applies to the sum and its negative. Their union contains exactly the event that the absolute value is at least $t$, and adding the two tail estimates proves the claim.

**Key facts.** `FABL.uniformBooleanFunction_toMeasure_eq_pi`, `FABL.signValue_eq_neg_one_or_one`, `FABL.integral_signValue_uniformPMF`.
