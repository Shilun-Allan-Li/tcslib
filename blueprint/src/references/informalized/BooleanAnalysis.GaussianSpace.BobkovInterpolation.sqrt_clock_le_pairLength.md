<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.sqrt_clock_le_pairLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound by the clock parameter

**Claim.** For all parameters, $\sqrt c\le L(t,c)$, with the real square root understood to be zero when $c<0$.

**Proof.** Each radicand defining $L(t,c)$ is at least $c$: beyond $c$, it adds a square and a finite sum of squares, all nonnegative. Monotonicity of the real square root therefore bounds each of the two square roots below by $\sqrt c$. Their average is also at least $\sqrt c$.
