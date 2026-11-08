<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_log_gaussianBadTail_div_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Bad-Tail Logarithmic Rate

**Claim.** For fixed $0<\rho<1$, the logarithm of the shifted Gaussian tail, divided by $t^2$, tends to $-1/(2\rho^2)$ as $t\to+\infty$.

**Proof.** Set $s=(t-1)/\rho$. The shift-and-rescaling limit says $s\to+\infty$ (`tendsto_shift_div_correlation_atTop`). Applying the standard Gaussian upper-tail logarithmic rate along $s$ gives $\log Q(s)/s^2\to-1/2$ (`tendsto_log_standardGaussianUpperTail_div_sq`). Meanwhile, the squared-scale ratio satisfies $s^2/t^2\to1/\rho^2$ (`tendsto_shift_div_correlation_sq_div_sq`). Multiplying these limits yields $\log Q(s)/t^2\to-1/(2\rho^2)$. Since $Q(s)=B_\rho(t)$, this is the claimed rate.

**Key facts.** `FABL.tendsto_shift_div_correlation_atTop`, `FABL.tendsto_log_standardGaussianUpperTail_div_sq`, `FABL.tendsto_shift_div_correlation_sq_div_sq`.
