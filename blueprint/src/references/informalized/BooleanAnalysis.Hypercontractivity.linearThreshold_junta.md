<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Threshold.lean :: BooleanAnalysis.Hypercontractivity.linearThreshold_junta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Threshold Junta Approximation

**Claim.** There is a universal positive constant $C$ such that every $\{-1,1\}$-valued linear threshold function has, for the stated error and parameter ranges, a junta approximant with error at most $\varepsilon$ and size at most $I[f]^{2+\eta}(1/\eta)^{C/\varepsilon^2}$.

**Proof.** Choose a constant $B\geq1$ from the Fourier-tail cutoff theorem and set $C=200B$. For the given $f,\varepsilon,\eta$, total influence $I[f]$ is nonnegative, since it equals a sum of nonnegative squared Fourier coefficients weighted by degrees. Split into two cases.

1. If $I[f]=0$, the Fourier-weight-above-zero bound shows that all nonconstant Fourier weight vanishes: cube variance is bounded by that tail weight. The constant-approximation lemma supplies a Boolean constant junta with disagreement probability at most half the variance, hence at most $\varepsilon$. Its coordinate set is empty, and the required size bound reduces to $0\leq0$.

2. If $I[f]\ne0$, nonnegativity makes $I[f]>0$. The cutoff theorem gives a degree threshold $k\leq B/\varepsilon^2$ whose Fourier tail is at most $\varepsilon$. The optimized junta-from-tail theorem then supplies an approximant with the desired Boolean and junta properties, error at most $\varepsilon$, and size bounded by $I[f]^{2+\eta}/(\varepsilon(\eta/(2+\eta))^k)^{1+\eta}$. Apply the junta-size estimate to bound the denominator factor's reciprocal by $(1/\eta)^{200B/\varepsilon^2}$. Combining the bounds gives the claimed size with $C=200B$.

**Key facts.** `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`, `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`, `BooleanAnalysis.Hypercontractivity.fourierWeightAbove_le_totalInfluence_div_succ`, `BooleanAnalysis.Hypercontractivity.exists_boolean_constant_approximation`, `BooleanAnalysis.Hypercontractivity.linearThreshold_fourier_cutoff`, `BooleanAnalysis.Hypercontractivity.optimized_junta_of_fourier_tail`, `BooleanAnalysis.Hypercontractivity.linearThreshold_junta_size_bound`.
