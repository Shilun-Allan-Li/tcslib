<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.integral_abs_gaussianProjection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Moment of a Gaussian Linear Form

**Claim.** For independent standard Gaussian coordinates $Z_i$ and real coefficients $a_i$, the absolute first moment of $\sum_i a_iZ_i$ is $\sqrt{\sum_i a_i^2}\,2\varphi(0)$.

**Proof.** First, $\sum_i a_i^2\geq0$. If this sum is zero, every coefficient is zero, so both sides vanish. Otherwise let $r=\sqrt{\sum_i a_i^2}>0$ and set $b_i=a_i/r$. Then $\sum_i b_i^2=1$. The Gaussian projection theorem (`measurePreserving_gaussianProjection`) says that $\sum_i b_iZ_i$ has the standard one-dimensional Gaussian distribution. Since $\sum_i a_iZ_i=r\sum_i b_iZ_i$ and $r>0$, its absolute value is $r\left|\sum_i b_iZ_i\right|$. Its expected absolute value is consequently $r$ times the first absolute moment of a standard Gaussian, which is $2\varphi(0)$ (`integral_abs_standardGaussian`).

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianProjection`, `BooleanAnalysis.GaussianSpace.integral_abs_standardGaussian`.
