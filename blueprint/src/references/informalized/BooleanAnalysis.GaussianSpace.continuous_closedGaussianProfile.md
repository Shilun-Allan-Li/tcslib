<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.GaussianSpace.continuous_closedGaussianProfile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Closed Gaussian Profile

**Claim.** The closed Gaussian profile, equal to the Gaussian isoperimetric profile on $(0,1)$ and zero elsewhere, is continuous on $\mathbb R$.

**Proof.** Fix $x\in\mathbb R$. If $x<0$, then every point sufficiently near $x$ remains below $0$, so the profile is constantly zero there. If $x=0$, continuity is supplied by the endpoint result that the profile is continuous at zero (`continuousAt_closedGaussianProfile_zero`). For $0<x<1$, the profile has derivative $-\mathrm{standardGaussianQuantile}(x)$ (`hasDerivAt_closedGaussianProfile`), and differentiability implies continuity. At $x=1$, use the endpoint continuity result (`continuousAt_closedGaussianProfile_one`). Finally, if $x>1$, points sufficiently near $x$ remain above $1$, where the profile is constantly zero. These cases cover every real $x$, proving continuity everywhere.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousAt_closedGaussianProfile_zero`, `BooleanAnalysis.GaussianSpace.hasDerivAt_closedGaussianProfile`, `BooleanAnalysis.GaussianSpace.continuousAt_closedGaussianProfile_one`.
