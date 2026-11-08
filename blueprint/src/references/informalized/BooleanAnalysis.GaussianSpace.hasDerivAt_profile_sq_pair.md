<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/TwoPoint.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_profile_sq_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a squared profile pair

**Claim.** Let $U$ be the Gaussian isoperimetric profile and $Q$ the total Gaussian quantile. If $a+t$ and $a-t$ lie in $(0,1)$, then the function $x\mapsto U(a+x)^2+kU(a-x)^2$ is differentiable at $t$, with derivative $-2U(a+t)Q(a+t)+2kU(a-t)Q(a-t)$.

**Proof.** Apply the derivative formula for the square of the Gaussian isoperimetric profile (\texttt{hasDerivAt\_gaussianIsoperimetric\_sq}) at $a+t$ and $a-t$, respectively. The maps $x\mapsto a+x$ and $x\mapsto a-x$ have derivatives $1$ and $-1$. The chain rule therefore gives derivative $-2U(a+t)Q(a+t)$ for the first term and $2U(a-t)Q(a-t)$ for the second squared profile; multiplying the latter term by the constant $k$ multiplies its derivative by $k$. Adding these derivatives gives the stated expression.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric_sq`.
