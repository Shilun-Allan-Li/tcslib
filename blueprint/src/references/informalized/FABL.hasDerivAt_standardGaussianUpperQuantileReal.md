<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.hasDerivAt_standardGaussianUpperQuantileReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Upper Quantile Derivative

**Claim.** For each $\alpha\in(0,1)$, the real-valued standard Gaussian upper quantile is differentiable at $\alpha$, with derivative the negative reciprocal of the Gaussian isoperimetric profile there.

**Proof.** For $\beta$ in a neighborhood of $\alpha$ contained in $(0,1)$, the upper quantile and upper-tail functions are local inverses: the upper tail evaluated at the upper quantile of $\beta$ equals $\beta$ (`FABL.standardGaussianUpperTail_quantile`). The quantile is continuous at $\alpha$ (`FABL.continuousAt_standardGaussianUpperQuantileReal`). The upper tail has derivative $-\phi(t)$ (`FABL.hasDerivAt_standardGaussianUpperTail`), which is nonzero at the quantile because the Gaussian density is positive. The derivative rule for a differentiable function's local inverse therefore gives the quantile derivative $1/(-\phi(q_\alpha))$. On $(0,1)$, the isoperimetric profile equals $\phi(q_\alpha)$ (`FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo`), so this is the negative reciprocal of that profile.

**Key facts.** `FABL.standardGaussianUpperQuantileReal_eq`, `FABL.standardGaussianUpperTail_quantile`, `FABL.continuousAt_standardGaussianUpperQuantileReal`, `FABL.hasDerivAt_standardGaussianUpperTail`, `FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo`.
