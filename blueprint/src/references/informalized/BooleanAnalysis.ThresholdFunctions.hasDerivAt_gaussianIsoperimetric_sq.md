<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Squared Gaussian Profile

**Claim.** For $a\in(0,1)$, the function $p\mapsto I(p)^2$ is differentiable at $a$ with derivative $-2I(a)Q(a)$.

**Proof.** The Gaussian profile $I$ has derivative $I'(a)=-Q(a)$ at every $a\in(0,1)$ (\texttt{hasDerivAt_gaussianIsoperimetric}). Applying the power rule to its square gives derivative $2I(a)I'(a)$. Substituting the derivative of $I$ yields $-2I(a)Q(a)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric`.
