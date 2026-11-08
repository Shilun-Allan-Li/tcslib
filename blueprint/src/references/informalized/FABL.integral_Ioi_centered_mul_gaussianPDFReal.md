<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.integral_Ioi_centered_mul_gaussianPDFReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail Integral Identity

**Claim.** For $\mu,t\in\mathbb{R}$ and $v>0$, the integral of $(x-\mu)g_{\mu,v}(x)$ over $(t,\infty)$ equals $v g_{\mu,v}(t)$.

**Proof.** Let $F(x)=-v g_{\mu,v}(x)$. The derivative formula for the Gaussian density shows that $F'(x)=(x-\mu)g_{\mu,v}(x)$ for every $x$ (`FABL.hasDerivAt_gaussianPDFReal_posVariance`). This derivative is integrable on $(t,\infty)$ by integrability of the centered Gaussian density (`FABL.integrable_centered_mul_gaussianPDFReal`). Moreover, the Gaussian density tends to zero at $+\infty$, so $F(x)$ tends to zero there (`FABL.tendsto_gaussianPDFReal_posVariance_atTop`). The fundamental theorem of calculus on the half-line now gives the integral as $F(+\infty)-F(t)=0-(-v g_{\mu,v}(t))=v g_{\mu,v}(t)$.

**Key facts.** `FABL.hasDerivAt_gaussianPDFReal_posVariance`, `FABL.integrable_centered_mul_gaussianPDFReal`, `FABL.tendsto_gaussianPDFReal_posVariance_atTop`.
