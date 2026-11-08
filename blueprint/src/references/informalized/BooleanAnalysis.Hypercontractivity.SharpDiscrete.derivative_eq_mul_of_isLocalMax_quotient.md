<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.derivative_eq_mul_of_isLocalMax_quotient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative Condition at a Quotient Maximum

**Claim.** If $f$ and $g$ have derivatives $a$ and $b$ at $x$, respectively, $g(x)=1$, and $f/g^r$ has a local maximum at $x$, then $a=r f(x)b$.

**Proof.** Since $g(x)=1$, the function $g(t)^r$ is defined near $x$ and is nonzero at $x$. The quotient rule and chain rule therefore show that $t\mapsto f(t)/g(t)^r$ is differentiable at $x$. A differentiable function at a local maximum has derivative zero. Evaluating that derivative at $x$, where $g(x)=1$, gives $a-rf(x)b=0$, and rearranging yields the asserted identity.
