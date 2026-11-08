<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantAtThreshold_lower_tail_rpow_div_quantilePower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail-Power Lower Bound

**Claim.** For $0<\rho<1$ and $t\ge1$, the Gaussian quadrant probability is at least the Gaussian quadrant polylogarithmic constant times the standard upper tail raised to $2/(1+\rho)$, divided by $t^{2-2/(1+\rho)}$.

**Proof.** Let $a=2/(1+\rho)$. The standard Gaussian upper tail is positive, and the upper Mills bound says it is at most $\phi(t)/t$ (\texttt{standardGaussianUpperTail\_le\_density\_div}); since $a\ge0$, raising both sides to $a$ preserves the inequality. Also $t^{2-a}>0$, and the polylogarithmic constant is positive (\texttt{gaussianQuadrantPolylogConstant\_pos}), so multiplying by that constant and dividing by $t^{2-a}$ preserves the bound. The normalized Mills identity rewrites the resulting expression exactly as $C_\rho e^{-t^2/(1+\rho)}/t^2$ (\texttt{normalized\_mills\_power\_eq\_exp\_div\_sq}). The exponential lower bound for the quadrant probability then finishes the proof (\texttt{gaussianQuadrantAtThreshold\_lower\_exp\_div\_sq}).

**Key facts.** `FABL.standardGaussianUpperTail_pos`, `FABL.standardGaussianUpperTail_le_density_div`, `FABL.gaussianQuadrantPolylogConstant_pos`, `FABL.normalized_mills_power_eq_exp_div_sq`, `FABL.gaussianQuadrantAtThreshold_lower_exp_div_sq`.
