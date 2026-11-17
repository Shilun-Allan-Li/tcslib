<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Continuity.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_tendsto_zero_L1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise converges to its mean in $L^1$

**Claim.** For every integrable $f$, as the correlation $\rho$ tends to zero, the $L^1$ distance between Gaussian noise applied to $f$ and the mean of $f$ tends to zero.

**Proof.** For all $\rho$ sufficiently close to zero, $\rho\in[-1,1]$. The noise-to-mean $L^1$ distance is bounded by the product-space $L^1$ distance between $f$ evaluated at the correlated affine combination of two independent Gaussian vectors and $f$ evaluated at the second vector (\texttt{eLpNorm\_gaussianNoise\_sub\_mean\_le}). Near zero, write $\rho=\cos(\arccos\rho)$ and $\sqrt{1-\rho^2}=\sin(\arccos\rho)$. The resulting product-space expression is the endpoint distance between the Gaussian transforms with angle $\arccos\rho$ and the transform at angle $\arccos 0$. This distance tends to zero by continuity of the endpoint $L^1$ norm (\texttt{tendsto\_eLpNorm\_gaussianEndpoint\_at}), applied at $c=0$. The noise-to-mean distance is nonnegative and bounded above by a quantity tending to zero, so it too tends to zero.

**Key facts.** `BooleanAnalysis.GaussianSpace.eLpNorm_gaussianNoise_sub_mean_le`, `BooleanAnalysis.GaussianSpace.tendsto_eLpNorm_gaussianEndpoint_at`.
