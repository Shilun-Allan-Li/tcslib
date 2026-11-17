<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.integral_Ioi_mul_exp_neg_half_mul_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Exponential Tail Integral

**Claim.** For every real $t$, the integral of $x\exp(-x^2/2)$ over $x>t$ equals $\exp(-t^2/2)$.

**Proof.** The function $F(x)=-\exp(-x^2/2)$ has derivative $x\exp(-x^2/2)$. This integrand is integrable on every half-line $(t,\infty)$. Also $F(x)\to0$ as $x\to\infty$, since the exponent tends to $-\infty$. The fundamental theorem of calculus for an improper integral therefore gives the integral as $0-F(t)=\exp(-t^2/2)$.
