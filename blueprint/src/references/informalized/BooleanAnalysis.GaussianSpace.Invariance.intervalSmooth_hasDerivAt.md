<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Smoothing.lean :: BooleanAnalysis.GaussianSpace.Invariance.intervalSmooth_hasDerivAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Translated Interval Average

**Claim.** For positive $\eta$ and continuous $\psi$, the translated interval average has derivative $\bigl(\psi(x+\eta)-\psi(x)\bigr)/\eta$ at each $x$.

**Proof.** Let $P(y)=\int_0^y\psi(t)\,dt$. By the fundamental theorem of calculus, $P$ is differentiable at every point $u$ with derivative $\psi(u)$. Changing variables in the interval average shows that $S_\eta\psi(y)=(P(y+\eta)-P(y))/\eta$. Differentiating this expression at $x$ gives $(\psi(x+\eta)-\psi(x))/\eta$, as claimed.
