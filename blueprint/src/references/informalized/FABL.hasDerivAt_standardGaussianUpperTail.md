<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.hasDerivAt_standardGaussianUpperTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Upper Tail Derivative

**Claim.** At every real $t$, the standard Gaussian upper-tail function is differentiable with derivative equal to the negative standard Gaussian density at $t$.

**Proof.** Express the upper tail at any $u$ as its value at $0$ minus the integral of the standard Gaussian density from $0$ to $u$ (`FABL.standardGaussianUpperTail_eq_anchor_integral`). The density is continuous (`FABL.continuous_standardGaussianDensity`), so the fundamental theorem of calculus gives derivative $\phi(t)$ for that integral at $t$. Subtracting it from the constant anchor value gives upper-tail derivative $-\phi(t)$.

**Key facts.** `FABL.standardGaussianUpperTail_eq_anchor_integral`, `FABL.continuous_standardGaussianDensity`.
