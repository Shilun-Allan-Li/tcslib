<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanCharacteristic.lean :: BooleanAnalysis.GaussianSpace.tendsto_sum_noiseKernel_normalizedCubeBlocks_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian limit of cube noise phases

**Claim.** For $\rho\in[-1,1]$ and $a,b\in\mathbb R^n$, the normalized average of the noise kernel times the phase of the normalized cube block sums converges to the expectation of the corresponding phase under the correlated Gaussian measure.

**Proof.** For each coordinate $i$, the correlated sign characteristic evaluated at $a_i/\sqrt m$ and $b_i/\sqrt m$, raised to the $m$th power, converges to $\exp\bigl(-(a_i^2+b_i^2+2\rho a_i b_i)/2\bigr)$ (by $\texttt{tendsto_correlatedSignCharacteristic_pow}$). Since there are only finitely many coordinates, taking the product preserves convergence. The finite product of these exponentials is the exponential of the sum of their exponents, namely $\exp\bigl(-\sum_i(a_i^2+b_i^2+2\rho a_i b_i)/2\bigr)$. The exact finite-cube phase identity ($\texttt{sum_noiseKernel_normalizedCubeBlocks_phase}$) identifies the sequence of normalized averages with the product sequence. The characteristic-function formula for the correlated Gaussian measure ($\texttt{integral_exp_correlatedGaussianMeasure}$), applicable because $\rho\in[-1,1]$, identifies the product limit with the stated Gaussian expectation.

**Key facts.** `BooleanAnalysis.GaussianSpace.tendsto_correlatedSignCharacteristic_pow`, `BooleanAnalysis.GaussianSpace.sum_noiseKernel_normalizedCubeBlocks_phase`, `BooleanAnalysis.GaussianSpace.integral_exp_correlatedGaussianMeasure`.
