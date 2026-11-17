<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.cubeLpNorm_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment Norm Identity

**Claim.** For every real-valued function on the Boolean cube, its power mean of order two equals its $L^2$ norm: $(\mathbb E|f|^2)^{1/2}=\sqrt{\mathbb E[f^2]}$.

**Proof.** At exponent two, $|f(x)|^2=f(x)^2$ for each point. The power mean therefore becomes the square root of the expectation of $f^2$, which is exactly the definition of the $L^2$ norm.
