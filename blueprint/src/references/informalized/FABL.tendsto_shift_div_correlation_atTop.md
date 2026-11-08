<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_shift_div_correlation_atTop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Quotient Divergence

**Claim.** For every real $\rho$ with $0<\rho<1$, $(t-1)/\rho$ tends to $+\infty$ as $t$ tends to $+\infty$.

**Proof.** First, translating the identity function by the constant $-1$ preserves its limit at $+\infty$, so $t-1\to+\infty$. Since $\rho>0$, dividing a function that tends to $+\infty$ by $\rho$ still gives a function tending to $+\infty$.
