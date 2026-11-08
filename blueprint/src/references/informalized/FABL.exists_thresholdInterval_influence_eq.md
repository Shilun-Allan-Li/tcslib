<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.exists_thresholdInterval_influence_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence at an Intermediate Threshold

**Claim.** For the stated monotone nonconstant Boolean function and $0<\varepsilon<1/2$, there is a bias parameter strictly between its lower and upper threshold parameters at error $\varepsilon$ where total product influence equals $\sigma(p)^2(1-2\varepsilon)/w$, with $w$ the threshold width.

**Proof.** Write $p_0$ and $p_1$ for the lower and upper threshold parameters. The critical probability lies strictly between them, so $p_0<p_1$. The biased minus-probability polynomial is continuous on $[p_0,p_1]$ and differentiable in its interior. The mean value theorem therefore supplies an interior point $p$ where its derivative equals the secant slope between the endpoint values. Its derivative at an interior point is total product influence divided by $\sigma(p)^2$. The endpoint values are $\varepsilon$ and $1-\varepsilon$, respectively, so the secant slope is $(1-2\varepsilon)/(p_1-p_0)$. Since $p$ lies in $(0,1)$, $\sigma(p)>0$; multiplying the derivative identity by $\sigma(p)^2$ is therefore valid and gives total influence equal to $\sigma(p)^2(1-2\varepsilon)/(p_1-p_0)$. The denominator is the threshold width $w$, as required.

**Key facts.** `FABL.thresholdLower_lt_critical_lt_thresholdUpper`, `FABL.continuous_biasedMinusProbabilityPolynomial`, `FABL.biasedProbabilityLevel_mem_Ioo`, `FABL.hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`, `FABL.biasedMinusProbabilityPolynomial_thresholdLowerParameter`, `FABL.biasedMinusProbabilityPolynomial_thresholdUpperParameter`, `FABL.biasSigma_pos`.
