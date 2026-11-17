<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.noiseOp_dim_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise on the Zero-Dimensional Cube

**Claim.** On the zero-dimensional Boolean cube, the noise operator fixes every function: $T_\rho f=f$.

**Proof.** By the Walsh expansion (`BooleanAnalysis.walsh_expansion`), the value of $f$ at any point is the sum of its Fourier terms over subsets of the coordinate set. In dimension zero the coordinate set is empty, so its only subset is $\varnothing$. The noise expansion for $T_\rho f$ therefore has just this same term; its multiplier is $\rho^{|\varnothing|}=1$. Hence the two functions agree at every point.

**Key facts.** `BooleanAnalysis.walsh_expansion`.
