<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Halfspace.lean :: BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_projection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection of the Correlated Gaussian Measure

**Claim.** If $a\in\mathbb R^n$ has squared norm $1$, projecting each vector in a correlated Gaussian pair onto $a$ gives the law obtained by applying the same correlation construction to two independent one-dimensional standard Gaussians.

**Proof.** Let $L(g)=\sum_i a_i g_i$. The unit-norm assumption implies that $L$ preserves standard Gaussian measure ($\texttt{measurePreserving\_gaussianProjection}$); hence applying $L$ separately to the two independent Gaussian vectors preserves their product law. Under this projection, the first component of the correlated pair becomes $L(g)$, while the second becomes $L(\rho g+\sqrt{1-\rho^2}g')$. By linearity, the latter equals $\rho L(g)+\sqrt{1-\rho^2}L(g')$. Therefore the projected pair is exactly the correlation construction applied to the two projected scalar Gaussians, yielding the stated equality of laws.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianProjection`.
