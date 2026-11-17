<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairDeficit_half_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step interpolation deficit bound

**Claim.** Under the stated nonnegativity and two-point inequality assumptions on $P$, the interpolation deficit at $(t,c)$ is at most half the deficit at $\bigl(|2t-1|,c+((1-t)b)^2\bigr)$.

**Proof.** Set $c_0=c+((1-t)b)^2$, which is nonnegative. The condition $0\le t\le1$ also gives $b^2(1-(2t-1)^2)\ge0$. Concavity of the length at displacement $1$ as a function of its nonnegative clock parameter (`concaveOn_pairLength_clock`), applied at $c_0$ and $c_0+b^2(1-(2t-1)^2)$ with equal weights, bounds its value at their midpoint by the average of its endpoint values. The midpoint parameter simplifies to $c+b^2(1-t^2)$. Separately, the adaptive midpoint bound (`pairLength_adaptive_midpoint`) bounds the length at $(t,c)$ by the average of the lengths at displacements $1$ and $2t-1$, both with clock $c_0$. In the deficit, the displacement $|2t-1|$ can be replaced by $2t-1$ without changing the length (`pairLength_abs`). Combining these bounds and rearranging gives the claimed half-step inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.concaveOn_pairLength_clock`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_adaptive_midpoint`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_abs`.
