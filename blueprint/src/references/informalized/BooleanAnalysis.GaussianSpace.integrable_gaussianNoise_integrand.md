<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Density.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianNoise_integrand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability under a Gaussian noise shift

**Claim.** For $\rho\in[-1,1]$, if $f$ is integrable under the product standard Gaussian measure on $\mathbb R^n$, then for each fixed $x$, the function $y\mapsto f(\rho x+\sqrt{1-\rho^2}\,y)$ is integrable under the same measure.

**Proof.** Set $s=\sqrt{1-\rho^2}$. If $s=0$, the shifted argument is the constant vector $\rho x$, so the function of $y$ is constant and hence integrable. Suppose $s\ne0$, and let $v=s^2>0$. Since $s^2=1-\rho^2$, we have $v+\rho^2=1$. The affine map $y\mapsto(\rho x_i+s y_i)_i$ sends the product standard Gaussian law to the product law whose $i$th coordinate is Gaussian with mean $\rho x_i$ and variance $v$ (measure preservation under Gaussian affine maps, `measurePreserving_gaussianAffine_pi`). This target measure is bounded above by a finite constant times the product standard Gaussian measure, by the Gaussian noise domination estimate (`pi_gaussianNoise_le_smul`). Thus integrability of $f$ under the standard product Gaussian implies integrability under the target law: multiplying the reference measure by that finite constant preserves integrability, and domination transfers it to the target measure. Pulling this integrable function back along the measure-preserving affine map gives the asserted integrability in $y$.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianAffine_pi`, `BooleanAnalysis.GaussianSpace.pi_gaussianNoise_le_smul`.
