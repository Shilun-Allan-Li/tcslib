<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/TorusApproximation.lean :: BooleanAnalysis.GaussianSpace.exists_gaussianTorus_approximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuous approximation on the Gaussian torus

**Claim.** For a finite measure on $\mathbb R^n$ and $1\le p<\infty$, every function in $L^p$ can be approximated by compositions of continuous functions on the torus, with convergence in $L^p$ and almost everywhere along a sequence.

**Proof.** Push the measure forward under the Gaussian torus map, obtaining a measure $\nu$ on the torus. Pullback along this map gives an isometric map from $L^p(\nu)$ to $L^p(\mu)$, since the map is continuous and measure preserving relative to the pushforward measure. The surjectivity of this pullback map (\texttt{surjective_gaussianTorus_pullback}) therefore gives an element $g\in L^p(\nu)$ whose pullback is the class of $f$. Continuous functions are dense in $L^p(\nu)$ when $p<\infty$, so choose continuous functions $F_m$ whose classes converge to $g$. Continuity of the pullback isometry implies that their compositions with the torus map converge to $f$ in $L^p(\mu)$. The representatives agree almost everywhere with the corresponding $L^p$ classes, so this also gives convergence of the stated $L^p$ errors to zero. This convergence implies convergence in measure; the subsequence principle for convergence in measure then supplies a subsequence converging to $f$ almost everywhere. Reindex that subsequence as the requested sequence. The torus map is continuous (\texttt{continuous_gaussianTorusMap}), ensuring the compositions used here are measurable.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuous_gaussianTorusMap`, `BooleanAnalysis.GaussianSpace.surjective_gaussianTorus_pullback`.
