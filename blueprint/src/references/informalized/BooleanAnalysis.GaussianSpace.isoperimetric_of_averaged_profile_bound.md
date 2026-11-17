<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SurfaceArea.lean :: BooleanAnalysis.GaussianSpace.isoperimetric_of_averaged_profile_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Isoperimetry from averaged profiles

**Claim.** If the closed Gaussian profile at an interior value $\alpha$ is bounded above by the averaged profile integral plus the Gaussian surface area of $A$ at every sufficiently small positive angle, then the Gaussian isoperimetric profile at $\alpha$ is bounded above by that surface area.

**Proof.** Let $G(u)$ be the integral of the closed Gaussian profile evaluated at the averaged Gaussian indicator of $A$. The convergence theorem for averaged profiles states that $G(u)\to0$ as $u\to0$ (\texttt{BooleanAnalysis.GaussianSpace.tendsto_integral_profile_averagedGaussianIndicator}); measurability of $A$ supplies its hypothesis. Continuity of the extended-real embedding $r\mapsto\operatorname{ofReal}(r)$ gives $\operatorname{ofReal}(G(u))\to0$, so the assumed upper bounds have right-hand sides tending to the Gaussian surface area of $A$. Restrict to positive $u<\pi/2$, which form a neighborhood of zero from the right. Because $\alpha\in(0,1)$, its closed profile equals its Gaussian isoperimetric profile. Passing the pointwise inequality to the limit therefore gives $\operatorname{ofReal}(\text{Gaussian isoperimetric profile at }\alpha)\le\text{Gaussian surface area of }A$.

**Key facts.** `BooleanAnalysis.GaussianSpace.tendsto_integral_profile_averagedGaussianIndicator`.
