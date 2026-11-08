<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.sinh_ratio_antitoneOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of a hyperbolic sine ratio

**Claim.** For $0\le a\le1$, the function $u\mapsto\sinh(au)/\sinh u$ is nonincreasing on $u>0$.

**Proof.** On $u>0$ the quotient is differentiable, with derivative numerator $a\cosh(au)\sinh u-\sinh(au)\cosh u$ and positive denominator $\sinh^2u$. Concavity of $\tanh$ on the nonnegative half-line, applied to $au=a\,u+(1-a)\,0$, gives $a\tanh u\le\tanh(au)$. Rewriting this inequality using $\tanh x=\sinh x/\cosh x$ and the positivity of the hyperbolic cosines shows that the derivative numerator is nonpositive. Hence the derivative is nonpositive throughout the positive half-line, and the function is nonincreasing there.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.concaveOn_tanh_nonneg`.
