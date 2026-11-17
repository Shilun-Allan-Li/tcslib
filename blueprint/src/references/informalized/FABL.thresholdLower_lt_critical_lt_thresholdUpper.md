<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.thresholdLower_lt_critical_lt_thresholdUpper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold interval surrounds the critical point

**Claim.** For a nonconstant monotone Boolean function and $0<\varepsilon<1/2$, the parameter at which its biased probability is $\varepsilon$ lies below the critical parameter, and the parameter at which it is $1-\varepsilon$ lies above it.

**Proof.** Write $p_0$ for the lower threshold parameter, $p_c$ for the critical probability, and $p_1$ for the upper threshold parameter. Each lies in $(0,1)$, by the interior-level results for biased probability levels and the critical probability (`biasedProbabilityLevel_mem_Ioo`, `criticalProbability_mem_Ioo`). The biased minus probability polynomial is strictly increasing on $[0,1]$ (`strictMonoOn_biasedMinusProbabilityPolynomial`). At these three parameters its values are respectively $\varepsilon$, $1/2$, and $1-\varepsilon$ (`biasedMinusProbabilityPolynomial_thresholdLowerParameter`, `biasedMinusProbabilityPolynomial_criticalProbability`, `biasedMinusProbabilityPolynomial_thresholdUpperParameter`). If $p_c\le p_0$, monotonicity would give $1/2\le\varepsilon$, contradicting $\varepsilon<1/2$. If $p_1\le p_c$, it would give $1-\varepsilon\le1/2$, again contradicting $\varepsilon<1/2$. Thus $p_0<p_c<p_1$.

**Key facts.** `FABL.biasedProbabilityLevel_mem_Ioo`, `FABL.criticalProbability_mem_Ioo`, `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`, `FABL.biasedMinusProbabilityPolynomial_thresholdLowerParameter`, `FABL.biasedMinusProbabilityPolynomial_criticalProbability`, `FABL.biasedMinusProbabilityPolynomial_thresholdUpperParameter`.
