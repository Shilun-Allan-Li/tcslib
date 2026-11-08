<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_profile_sq_pair_derivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a profile pair derivative

**Claim.** Let $U$ be the Gaussian isoperimetric profile and $Q$ the total Gaussian quantile. If $a+t$ and $a-t$ lie in $(0,1)$, then $x\mapsto-2U(a+x)Q(a+x)+2kU(a-x)Q(a-x)$ is differentiable at $t$, with derivative $2\bigl(Q(a+t)^2+kQ(a-t)^2-1-k\bigr)$.

**Proof.** Use the derivative formula for the product $U(p)Q(p)$ (\texttt{hasDerivAt\_gaussianIsoperimetric\_mul\_standardGaussianQuantile}) at $p=a+t$ and $p=a-t$. Its derivative is $1-Q(p)^2$. Composing with $x\mapsto a+x$ preserves this derivative, while composing with $x\mapsto a-x$ changes its sign. The constant factors $-2$ and $2k$ then give contributions $-2(1-Q(a+t)^2)$ and $-2k(1-Q(a-t)^2)$. Their sum is the claimed expression after collecting terms.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric_mul_standardGaussianQuantile`.
