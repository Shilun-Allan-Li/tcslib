<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.concaveOn_tanh_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concavity of Hyperbolic Tangent

**Claim.** The function $x\mapsto\tanh x$ is concave on $[0,\infty)$.

**Proof.** For every real $x$, differentiating $\tanh x=\sinh x/\cosh x$ and using $\cosh^2x-\sinh^2x=1$ gives $(\tanh x)'=1/\cosh^2x$. On $[0,\infty)$, $\cosh$ is positive and increasing. Thus, whenever $0\le x\le y$, we have $\cosh x\le\cosh y$, and hence $1/\cosh^2y\le1/\cosh^2x$. The derivative of $\tanh$ is therefore antitone on this interval. The derivative criterion for concavity on a convex interval yields the result.
