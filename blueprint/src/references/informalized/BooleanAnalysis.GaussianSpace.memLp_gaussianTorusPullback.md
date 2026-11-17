<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/TorusApproximation.lean :: BooleanAnalysis.GaussianSpace.memLp_gaussianTorusPullback -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Continuous Torus Pullback

**Claim.** For a finite measure $\mu$, every continuous real-valued function on the specified torus, composed with the torus map from $\mathbb R^n$, belongs to $L^p(\mu)$ for every $p\in[0,\infty]$.

**Proof.** The torus map is continuous (BooleanAnalysis.GaussianSpace.continuous_gaussianTorusMap), so its composition with the continuous function $F$ is continuous and hence measurable. Since the torus is compact, $F$ is bounded by its supremum norm. Thus the composition is bounded everywhere. A measurable bounded function on a finite measure space belongs to $L^p$ for every exponent, including $p=\infty$.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuous_gaussianTorusMap`.
