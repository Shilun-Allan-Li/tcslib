<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Affine.lean :: BooleanAnalysis.GaussianSpace.gaussianNoiseStability_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Gaussian noise stability

**Claim.** Let $\rho\in[-1,1]$, and let $f:\mathbb R^n\to\mathbb R$ belong to $L^2$ under the product standard Gaussian measure. For all $a,b\in\mathbb R$, the stability of $x\mapsto af(x)+b$ is $a^2$ times the stability of $f$, plus $2ab$ times the Gaussian mean of $f$, plus $b^2$.

**Proof.** First, the $L^2$ hypothesis makes $f$ integrable. The Gaussian noise operator preserves the relevant $L^2$ class (\texttt{gaussianNoise\_memLp}), so its value on $f$ is integrable as well; the product $f\,T_\rho f$ is integrable by the $L^2$ product estimate. Linearity of the noise operator (\texttt{gaussianNoise\_add}) and its behavior under scalar multiplication (\texttt{gaussianNoise\_const\_mul}), together with its value on a constant, give $T_\rho(af+b)=aT_\rho f+b$. Substituting this into the defining stability integral and expanding the product yields four terms: $a^2fT_\rho f$, $abf$, $abT_\rho f$, and $b^2$. Their integrability follows from the preceding bounds. Integrating term by term, the first contributes $a^2$ times the stability of $f$, while the second and third each contribute $ab$ times the mean of $f$: for the third, use preservation of the integral by the noise operator (\texttt{integral\_gaussianNoise}). The constant term integrates to $b^2$, since the Gaussian measure is a probability measure. Combining the terms gives the stated formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianNoise_memLp`, `BooleanAnalysis.GaussianSpace.gaussianNoise_add`, `BooleanAnalysis.GaussianSpace.gaussianNoise_const_mul`, `BooleanAnalysis.GaussianSpace.integral_gaussianNoise`.
