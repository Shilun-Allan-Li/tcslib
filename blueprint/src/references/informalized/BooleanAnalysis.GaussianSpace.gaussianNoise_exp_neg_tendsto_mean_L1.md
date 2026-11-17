<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Continuity.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_exp_neg_tendsto_mean_L1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Long-time Gaussian noise convergence

**Claim.** For every integrable function $f$, the $L^1$ distance between Gaussian noise of correlation $e^{-t}$ applied to $f$ and the mean of $f$ tends to zero as $t$ tends to infinity.

**Proof.** The previously established limit says that as the correlation parameter $\rho$ tends to $0$, Gaussian noise applied to $f$ converges in $L^1$ to its mean (\texttt{gaussianNoise\_tendsto\_zero\_L1}). As $t\to\infty$, the parameter $e^{-t}$ tends to $0$: negation sends $t\to\infty$ to $-t\to-\infty$, and the exponential tends to zero at $-\infty$. Composing these limits gives the asserted convergence.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianNoise_tendsto_zero_L1`.
