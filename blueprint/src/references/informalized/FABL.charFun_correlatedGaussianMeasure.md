<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.charFun_correlatedGaussianMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characteristic function of a correlated Gaussian

**Claim.** For $\rho\in[-1,1]$ and $t=(t_1,t_2)\in\mathbb R^2$, the characteristic function of the correlated Gaussian measure at $t$ is $\exp(-(t_1^2+2\rho t_1t_2+t_2^2)/2)$.

**Proof.** The correlated Gaussian is the image of a pair of independent standard Gaussians under the map $(u,v)\mapsto (u,\rho u+\sqrt{1-\rho^2}\,v)$. The inner product of this image with $t$ splits into the sum of $u$ times $t_1+\rho t_2$ and $v$ times $\sqrt{1-\rho^2}\,t_2$ (FABL.inner_gaussianCorrelationMap). Accordingly, its characteristic function factors into the characteristic functions of the two independent standard Gaussian coordinates. Each is the standard Gaussian characteristic function $a\mapsto e^{-a^2/2}$. Combining the exponents gives $-\tfrac12((t_1+\rho t_2)^2+(1-\rho^2)t_2^2)=-\tfrac12(t_1^2+2\rho t_1t_2+t_2^2)$, as required.

**Key facts.** `FABL.inner_gaussianCorrelationMap`.
