<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.memLp_gaussianGeneratorQuotient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square Integrability of the Gaussian Noise Quotient

**Claim.** If $f$ is square-integrable and $t\ge0$, then $x\mapsto(f(x)-T_{e^{-t}}f(x))/t$ is square-integrable for product standard Gaussian measure.

**Proof.** The correlation parameter $e^{-t}$ lies in $[-1,1]$ whenever $t\ge0$ (BooleanAnalysis.GaussianSpace.exp_neg_mem_correlationInterval). The Gaussian noise operator therefore preserves $L^2$: $T_{e^{-t}}f$ is square-integrable by the noise-operator membership theorem (BooleanAnalysis.GaussianSpace.gaussianNoise_memLp). The difference of two $L^2$ functions is in $L^2$, and multiplication by the scalar $1/t$ preserves $L^2$. This gives the stated quotient, including at $t=0$, where the pointwise quotient is interpreted by the function's given definition.

**Key facts.** `BooleanAnalysis.GaussianSpace.exp_neg_mem_correlationInterval`, `BooleanAnalysis.GaussianSpace.gaussianNoise_memLp`.
