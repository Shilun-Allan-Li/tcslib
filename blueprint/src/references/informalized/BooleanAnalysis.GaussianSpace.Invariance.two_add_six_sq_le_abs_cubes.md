<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.two_add_six_sq_le_abs_cubes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Absolute Cubes Bound

**Claim.** For every real $t$, $2+6t^2\le |1+t|^3+|1-t|^3$.

**Proof.** Split into three ranges. If $t<-1$, then $1+t<0$ and $1-t>0$, so the right side is $( -1-t)^3+(1-t)^3$; expanding shows the inequality, equivalently a nonnegative cubic expression in $-t-1$. If $t>1$, the absolute values give $(1+t)^3+(t-1)^3$, and expansion again reduces the assertion to nonnegativity of a cubic expression in $t-1$. In the remaining range $-1\le t\le1$, both terms inside the absolute values are nonnegative, and expansion gives exactly $2+6t^2$.
