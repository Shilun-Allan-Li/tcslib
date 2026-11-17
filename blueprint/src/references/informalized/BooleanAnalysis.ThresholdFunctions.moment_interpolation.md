<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean :: BooleanAnalysis.ThresholdFunctions.moment_interpolation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpolation Between Moments

**Claim.** For a Boolean-cube function $f$ and $1<t<2$, its $t$th absolute moment is at most its first absolute moment raised to $2-t$ times its second moment raised to $t-1$.

**Proof.** Set $r=1/(t-1)$, so $r\ge1$ and $1/r=t-1$. On the finite Boolean cube, apply the weighted Hölder inequality with exponent $r$ to the nonnegative functions $w(x)=|f(x)|$ and $v(x)=|f(x)|^{t-1}$. The pointwise product is $w(x)v(x)=|f(x)|^t$, while $v(x)^r=|f(x)|$ because $(t-1)r=1$. Therefore the other product appearing in the weighted Hölder bound is $w(x)v(x)^r=|f(x)|^2=f(x)^2$. Rewriting the finite uniform averages as expectations gives $\mathbb E[|f|^t]\le (\mathbb E[|f|])^{1-1/r}(\mathbb E[f^2])^{1/r}$. Finally, $1/r=t-1$ and $1-1/r=2-t$, giving the claimed inequality.

**Key facts.** `BooleanAnalysis.expect_eq_fintypeExpect`.
