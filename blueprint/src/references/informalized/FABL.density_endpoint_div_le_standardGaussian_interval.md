<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.density_endpoint_div_le_standardGaussian_interval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density Bound on an Interval

**Claim.** For $t>0$, the standard Gaussian density at $t+1/t$, divided by $t$, is at most the standard Gaussian measure of $(t,t+1/t)$.

**Proof.** Write the interval's Gaussian measure as the integral of the standard Gaussian density over $(t,t+1/t)$ (\texttt{standardGaussian\_measureReal\_Ioo\_eq\_integral}). The interval has length $1/t$, so integrating the constant endpoint density over it gives $\text{density}(t+1/t)/t$. For every $x$ in the interval, $0<t<x<t+1/t$; the standard Gaussian density is decreasing on the nonnegative half-line, so its value at the right endpoint is no larger than its value at $x$ (\texttt{standardGaussianDensity\_antitone\_of\_nonneg}). Integrating this pointwise comparison over the interval proves the bound.

**Key facts.** `FABL.standardGaussian_measureReal_Ioo_eq_integral`, `FABL.standardGaussianDensity_antitone_of_nonneg`.
