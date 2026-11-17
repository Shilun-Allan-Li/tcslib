<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorSmoothing.lean :: BooleanAnalysis.GaussianSpace.integrable_averagedGaussianIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Averaged Gaussian Indicators

**Claim.** For every measurable $A\subseteq\mathbb R^n$ and real $\theta$, the averaged Gaussian indicator is integrable with respect to standard Gaussian measure.

**Proof.** The averaged Gaussian indicator is measurable by \texttt{measurable_averagedGaussianIndicator}. Its values lie in $[0,1]$ by \texttt{averagedGaussianIndicator_mem_unitInterval}, so its absolute value is bounded by the constant function $1$. Since the measure is a probability measure, that constant function is integrable. The domination criterion for integrability therefore gives the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurable_averagedGaussianIndicator`, `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_mem_unitInterval`.
