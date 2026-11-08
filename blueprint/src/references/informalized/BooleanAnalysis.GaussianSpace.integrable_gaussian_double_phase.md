<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussian_double_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a double Gaussian phase

**Claim.** For real $a,b$, fixed $x$, and integrable real-valued $f$ under $\gamma_n$, the product of the two Gaussian phases and $f(w)$ is integrable as a complex-valued function under $\gamma_n\otimes\gamma_n$.

**Proof.** The two-phase factor $(u,w)\mapsto\Phi_a(u,x)\Phi_b(w,u)$ is measurable, since the phase is a continuous exponential of the indicated finite sums and products. Each phase has norm one (`norm_gaussianPhase`), so their product also has norm one. The function $(u,w)\mapsto f(w)$ is integrable in norm under the product measure: its norm-integral reduces to that of $|f|$ under the second marginal, which is $\gamma_n$. Multiplying this integrable function by the measurable two-phase factor preserves strong measurability, and its norm is unchanged. Hence the product is integrable.

**Key facts.** `BooleanAnalysis.GaussianSpace.norm_gaussianPhase`.
