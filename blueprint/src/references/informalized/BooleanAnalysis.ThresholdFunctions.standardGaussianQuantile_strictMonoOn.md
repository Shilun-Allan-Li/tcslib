<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_strictMonoOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict monotonicity of the Gaussian quantile

**Claim.** The standard Gaussian quantile is strictly increasing on $(0,1)$: if $0<\alpha<\beta<1$, then $Q(\alpha)<Q(\beta)$.

**Proof.** Take $0<\alpha<\beta<1$. The standard Gaussian CDF is strictly increasing, so for any real numbers $u,v$, $u<v$ is equivalent to $\Phi(u)<\Phi(v)$ (strict monotonicity of the CDF, `standardGaussianCDF_strictMono`). Apply this equivalence to $u=Q(\alpha)$ and $v=Q(\beta)$. The quantile identity gives $\Phi(Q(\alpha))=\alpha$ and $\Phi(Q(\beta))=\beta$ (`standardGaussianCDF_quantile`), and the assumed inequality $\alpha<\beta$ therefore yields $Q(\alpha)<Q(\beta)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`.
