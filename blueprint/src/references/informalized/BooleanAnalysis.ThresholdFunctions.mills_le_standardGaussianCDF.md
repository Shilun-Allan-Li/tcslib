<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.mills_le_standardGaussianCDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mills Lower Bound

**Claim.** For every real $t<0$, the Mills expression $\mathrm{millsF}(t)$ is at most the standard Gaussian CDF at $t$.

**Proof.** Integrate the derivative of $\mathrm{millsF}$ over $(-\infty,t]$. The fundamental theorem for an improper integral applies because $\mathrm{millsF}$ is continuous and differentiable on this interval, its derivative is integrable there, and $\mathrm{millsF}(x)\to0$ as $x\to-\infty$. Thus $\int_{-\infty}^t \mathrm{millsF}'(x)\,dx=\mathrm{millsF}(t)$. For each $x\le t<0$, we have $x\ne0$ and $x^4>0$, so $1-3x^{-4}\le1$. The derivative formula gives $\mathrm{millsF}'(x)=\mathrm{standardGaussianPDF}(x)(1-3x^{-4})$; since the Gaussian density is positive, this is at most the density. Integrating this pointwise inequality yields $\mathrm{millsF}(t)\le\int_{-\infty}^t\mathrm{standardGaussianPDF}(x)\,dx$. The latter integral is the standard Gaussian CDF at $t$, by the integral representation of the CDF.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.continuousAt_millsF`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_millsF`, `BooleanAnalysis.ThresholdFunctions.integrableOn_millsF'`, `BooleanAnalysis.ThresholdFunctions.tendsto_millsF_atBot`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_eq_integral`.
