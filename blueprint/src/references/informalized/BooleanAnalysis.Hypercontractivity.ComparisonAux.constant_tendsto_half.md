<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.constant_tendsto_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison constant at one half

**Claim.** Let $C(\lambda)$ equal $e$ at $\lambda=1/2$ and equal $((1-\lambda)/\lambda)^{1/(2(1-2\lambda))}$ otherwise, with the stated real-power conventions. As $\lambda$ tends to $1/2$ from below through $(0,1/2)$, $C(\lambda)$ tends to $e$.

**Proof.** Let $f(x)=\log((1-x)/x)$. Differentiating at $x=1/2$ gives $f'(1/2)=-4$. Thus the difference quotient $\bigl(f(\lambda)-f(1/2)\bigr)/(\lambda-1/2)$ tends to $-4$. Since $f(1/2)=0$, it follows that $f(\lambda)/[-4(\lambda-1/2)]$ tends to $1$. For $\lambda<1/2$, the exponent in the definition of $C$ satisfies $1/[2(1-2\lambda)]=-1/[4(\lambda-1/2)]$, so the logarithm of the displayed power defining $C(\lambda)$ is exactly $f(\lambda)/[-4(\lambda-1/2)]$. Its limit is therefore $1$. Continuity of the exponential function now gives $C(\lambda)\to e$.
