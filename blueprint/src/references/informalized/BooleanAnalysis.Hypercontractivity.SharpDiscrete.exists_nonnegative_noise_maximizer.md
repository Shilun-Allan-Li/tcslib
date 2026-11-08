<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.exists_nonnegative_noise_maximizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Noise Maximizer

**Claim.** There is a nonnegative vector on the weighted moment sphere that maximizes the quadratic noise functional over the entire sphere.

**Proof.** The weighted moment sphere is compact, and the functional $F$ is continuous because it is a finite sum of polynomial expressions in the coordinates. The sphere is nonempty: the constant vector with value $1$ has weighted moment $1$, by the normalization of the weights. The extreme value theorem therefore gives a point $f$ on the sphere at which $F$ attains its maximum. Set $g_i=|f_i|$. Then $g_i\geq 0$ and its weighted moment is unchanged, since $||f_i||=|f_i|$. To compare the functional values, the weighted triangle inequality gives $|\sum_i w_i f_i|\leq\sum_iw_i|f_i|$. Both sides inside this comparison are nonnegative after taking the absolute value on the left, so squaring preserves the inequality. The coefficient $1-\rho^2$ is nonnegative because $0\leq\rho\leq1$, while the other quadratic term is unchanged on replacing $f_i$ by $|f_i|$. Hence $F(f)\leq F(g)$. Since $f$ already maximizes $F$ on the sphere, $g$ does too.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_moment_sphere_compact`.
