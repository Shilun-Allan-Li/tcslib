<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.profile_sq_central_deficit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Central squared-profile deficit

**Claim.** If $b\ge0$, $a-b>0$, and $a+b<1$, then the stated lower bound on the symmetric squared-profile deficit holds.

**Proof.** Consider the convex function on $[-b,b]$ given by the sum of the two shifted squared Gaussian profiles and the quadratic correction $2(1-Q(a)^2)x^2$ (`convexOn_profile_sq_deficit`). Convexity at the midpoint says that its value at $0$ is at most the average of its values at $-b$ and $b$. The midpoint is the equal-weight average of these endpoints, and the assumptions ensure the convexity result applies. Substitute these three points into that inequality. The profile terms at $-b$ and $b$ exchange places, while the quadratic terms contribute $2(1-Q(a)^2)b^2$ at each endpoint and vanish at zero. Rearranging the resulting inequality gives the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.convexOn_profile_sq_deficit`.
