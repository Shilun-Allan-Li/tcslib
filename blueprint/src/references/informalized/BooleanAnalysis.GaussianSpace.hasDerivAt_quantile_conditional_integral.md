<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/ProfileCalculus.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_quantile_conditional_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a quantile conditional integral

**Claim.** Let $\gamma$ be standard Gaussian measure, $\Phi$ its distribution function, and $Q$ the total Gaussian quantile. For $a\in(0,1)$, the function $p\mapsto\int_{(-\infty,Q(p)]}\Phi((t-\rho x)/d)\,d\gamma(x)$ is differentiable at $a$, with derivative $\Phi((t-\rho Q(a))/d)$.

**Proof.** Set $f(x)=\varphi(x)\Phi((t-\rho x)/d)$, where $\varphi$ is the standard Gaussian density. Continuity of the density and distribution function, together with continuity of the affine argument, makes $f$ continuous. Also, $0<\Phi<1$ and $\varphi>0$, so $|f(x)|\leq\varphi(x)$; integrability of the Gaussian density implies that $f$ is integrable. Expressing the Gaussian integral over $(-\infty,b]$ as the ordinary integral of $f$ there (\texttt{integral\_Iic\_standardGaussianMeasure}), the fundamental theorem for integrals with a moving endpoint gives derivative $f(b)$ (\texttt{hasDerivAt\_integral\_Iic}). Now take $b=Q(p)$ and apply the chain rule. The quantile has derivative $1/U(a)$ at $a$ (\texttt{hasDerivAt\_standardGaussianQuantile}), so the resulting derivative is $f(Q(a))/U(a)$. Since $U(a)=\varphi(Q(a))>0$, this simplifies to $\Phi((t-\rho Q(a))/d)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_Iic_standardGaussianMeasure`, `BooleanAnalysis.GaussianSpace.hasDerivAt_integral_Iic`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`.
