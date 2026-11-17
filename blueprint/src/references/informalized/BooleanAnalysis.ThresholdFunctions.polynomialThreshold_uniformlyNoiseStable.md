<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.polynomialThreshold_uniformlyNoiseStable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Noise Stability of Polynomial Thresholds

**Claim.** For each fixed degree bound $k$, the class of polynomial threshold functions of degree at most $k$ is uniformly noise-stable.

**Proof.** Apply the stated noise-sensitivity bound for positive degree to $\max(k,1)$. It supplies constants $C\geq0$ and a natural number $d$ such that each function in that degree class has noise sensitivity at most $C\sqrt{\delta}\,\log(1/\delta)^d$ for $0<\delta\leq1/2$. By monotonicity of polynomial threshold classes, a function of degree at most $k$ belongs to the class of degree at most $\max(k,1)$, so this bound applies to it as well. Take this displayed expression as the uniform error function. It is nonnegative on $[0,1/2]$: at $\delta=0$ it is zero by the defined value of the expression, and for positive $\delta$ both the square root and the logarithm are nonnegative, with the exponent a natural number. Finally, $\sqrt{\delta}\,\log(1/\delta)^d$ tends to zero as $\delta$ tends to zero from above (\texttt{tendsto_sqrt_mul_log_pow}); multiplying by $C$ preserves that limit. The criterion that a Boolean-valued class with such a vanishing nonnegative bound is uniformly noise-stable (\texttt{isUniformlyNoiseStable_of_bound}) completes the proof.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.kane_totalInfluence_bound`, `BooleanAnalysis.ThresholdFunctions.polynomialThresholdClass_mono`, `BooleanAnalysis.ThresholdFunctions.tendsto_sqrt_mul_log_pow`, `BooleanAnalysis.ThresholdFunctions.isUniformlyNoiseStable_of_bound`.

**Caveat.** The formal proof uses the noise-sensitivity consequence included in kane_totalInfluence_bound; it does not invoke the input-negation and identification argument described in the supplied informal theorem proof.
