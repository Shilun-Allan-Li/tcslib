<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_moment_sphere_compact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compactness of the Moment Sphere

**Claim.** For positive weights and positive exponent, the set of vectors whose weighted absolute moment equals one is compact.

**Proof.** The weighted moment is a continuous function of the vector: each coordinate contribution is a constant multiple of the continuous function $t\mapsto |t|^p$, and there are only finitely many coordinates. Thus its level set at $1$ is closed. It remains to bound that level set. For each coordinate $i$, nonnegativity of all summands implies $w_i|f_i|^p\leq\sum_jw_j|f_j|^p=1$. Since $w_i>0$ and $p>0$, this yields $|f_i|\leq(1/w_i)^{1/p}$. Hence every coordinate lies in a fixed closed bounded interval. The level set is a closed subset of the product of these finitely many compact intervals, and is therefore compact.
