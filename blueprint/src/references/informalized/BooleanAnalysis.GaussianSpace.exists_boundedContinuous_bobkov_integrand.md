<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.exists_boundedContinuous_bobkov_integrand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Bounded Continuous Bobkov Integrand

**Claim.** Under the stated continuity, range, and derivative bounds, there is a bounded continuous function equal pointwise to the square root of the Gaussian-profile square plus the sum of squared coordinate derivatives.

**Proof.** The profile is continuous on $[0,1]$, so compactness of that interval bounds its absolute value there by some constant $A$. Since every value of $f$ lies in this interval, $|U(f(x))|\le A$ for all $x$. Define $H(x)$ to be the displayed square root. It is continuous because the profile composed with $f$ and each coordinate evaluation of the continuous linear functional $D(x)$ are continuous, and sums, squares, and the square-root operation preserve continuity on the nonnegative radicand. For each coordinate unit vector $e_i$, the operator norm estimate gives $|D(x)e_i|\le\|D(x)\|\le M$. Hence the sum of the squared coordinate evaluations is at most $nM^2$, while the profile square is at most $A^2$. It follows that $0\le H(x)\le\sqrt{A^2+nM^2}$ uniformly in $x$. Thus $H$ is bounded and continuous, and taking it as the required function proves the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousOn_closedGaussianProfile`, `BooleanAnalysis.GaussianSpace.continuous_closedGaussianProfile`.
