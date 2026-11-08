<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.criticalProbability_composedMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Majority Critical Probability

**Claim.** For every natural number $m$, the critical probability of the specified composed majority function is $1/2$.

**Proof.** Fix $m$ and take the composed majority function, which is monotone and nonconstant (`FABL.composedMajority_monotone`, `FABL.composedMajority_isNonconstant`). Its critical probability lies in $(0,1)$ (`FABL.criticalProbability_mem_Ioo`), and $1/2$ also lies in that interval. The biased minus probability polynomial takes the value $1/2$ both at the critical probability (`FABL.biasedMinusProbabilityPolynomial_criticalProbability`) and at $1/2$ (`FABL.composedMajority_probability_one_half`). The polynomial is strictly monotone on $[0,1]$ (`FABL.strictMonoOn_biasedMinusProbabilityPolynomial`), hence injective there. Since both points lie in this interval and have the same value, they are equal.

**Key facts.** `FABL.composedMajority_monotone`, `FABL.composedMajority_isNonconstant`, `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`, `FABL.criticalProbability_mem_Ioo`, `FABL.biasedMinusProbabilityPolynomial_criticalProbability`, `FABL.composedMajority_probability_one_half`.
