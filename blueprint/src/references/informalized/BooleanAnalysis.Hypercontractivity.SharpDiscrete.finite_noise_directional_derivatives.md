<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_directional_derivatives -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Directional Derivatives of Weighted Forms

**Claim.** At a nonnegative vector, the directional derivatives of the weighted moment and quadratic noise functional are the stated weighted sums.

**Proof.** Along the line $g+th$, each coordinate is an affine function of $t$ with derivative $h_i$. Differentiating the weighted mean gives derivative $\sum_iw_ih_i$, and differentiating the weighted sum of coordinate squares gives $2\sum_iw_ig_ih_i$. The first functional is a finite sum of terms $w_i|g_i+th_i|^p$. The derivative of $|u|^p$ at a nonnegative base point $u=g_i$ is $p g_i^{p-1}$ when $g_i>0$; at $g_i=0$, the derivative is also zero because $p>1$. Summing these coordinate derivatives gives $p\sum_iw_ig_i^{p-1}h_i$. Finally, the second part of $F$ is the square of the weighted mean, whose derivative at zero is twice the mean at $g$ times the derivative of the mean. Combining this with the derivative of the weighted square sum and the coefficients in $F$ gives the displayed formula.
