<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.standardGaussianMeasure_symmDiff_Iic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Measure of Differing Halflines

**Claim.** For all $a,b\in\mathbb R$, the standard Gaussian measure of the symmetric difference of $(-\infty,a]$ and $(-\infty,b]$ is $|\Phi(b)-\Phi(a)|$.

**Proof.** First suppose $a\le b$. Then $(-\infty,a]\subseteq(-\infty,b]$, so their symmetric difference is the larger halfline with the smaller one removed. The measure of that difference is the measure of $(-\infty,b]$ minus that of $(-\infty,a]$, which is $\Phi(b)-\Phi(a)$. Monotonicity of measure makes this difference nonnegative, so it equals its absolute value. If instead $b\le a$, reverse the roles: the measure is $\Phi(a)-\Phi(b)$, again nonnegative, and this is $|\Phi(b)-\Phi(a)|$.
