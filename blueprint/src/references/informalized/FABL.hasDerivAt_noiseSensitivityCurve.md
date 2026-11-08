<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.hasDerivAt_noiseSensitivityCurve -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity Derivative

**Claim.** For every real-valued cube function and every real noise parameter, the derivative of the noise sensitivity curve is the total stable influence at correlation parameter $1-2\delta$.

**Proof.** Set $g(t)=1-2t$. Its derivative at $\delta$ is $-2$. The stability curve is differentiable at $g(\delta)$, with derivative equal to the total stable influence there (`deriv_stabilityCurve_eq_totalStableInfluence`); its differentiability is supplied by the finite Fourier-sum derivative formula (`hasDerivAt_stabilityCurve`). The chain rule gives the derivative of $t\mapsto \operatorname{Stab}_{1-2t}[f]$ as $-2$ times that total stable influence. Since noise sensitivity is one half of one minus this stability curve, its derivative is the negative of that derivative divided by two, yielding the claimed total stable influence.

**Key facts.** `FABL.hasDerivAt_stabilityCurve`, `FABL.deriv_stabilityCurve_eq_totalStableInfluence`.
