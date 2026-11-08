<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_maximizer_two_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Values at a Noise Maximizer

**Claim.** Every nonnegative maximizer satisfying the stated hypotheses takes at most two distinct values: there are $a,b\ge0$ such that each coordinate of $g$ equals one of them.

**Proof.** Stationarity gives $F(g)\ge1$ and, for every coordinate, $F(g)g_i^{p-1}-\rho^2g_i=(1-\rho^2)\sum_jw_jg_j$. Divide by the positive number $F(g)$. Thus every $g_i$ lies at the same level of the function $\phi(y)=y^{p-1}-(\rho^2/F(g))y$ on $[0,\infty)$. The function $y^{p-1}$ is strictly concave there because $0<p-1<1$; subtracting a linear function preserves strict concavity. A strictly concave function on an interval takes any fixed value at at most two points: three ordered points with the same value would force the middle value to be strictly above the chord between the outer two. Applying this fact to the common level of $\phi$ shows that the coordinates of $g$ take at most two values, both nonnegative.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_maximizer_stationarity`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_concave_level_two_values`.
