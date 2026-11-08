<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Holder.lean :: BooleanAnalysis.Hypercontractivity.ReverseMoments.expect_rpow_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of a power moment

**Claim.** If $u$ is pointwise nonnegative and positive at at least one point of the Boolean cube, then its uniform power moment $\mathbb E[u^r]$ is positive.

**Proof.** Choose a point $x$ with $u(x)>0$. At every point $z$, nonnegativity gives $u(z)^r\ge0$, while at the chosen point the real power is strictly positive because its base is positive. Thus the finite sum of these powers has nonnegative summands and at least one positive summand, so it is positive. The uniform weight $(1/2)^n$ is also positive; multiplying the sum by it proves that the expectation is positive.
