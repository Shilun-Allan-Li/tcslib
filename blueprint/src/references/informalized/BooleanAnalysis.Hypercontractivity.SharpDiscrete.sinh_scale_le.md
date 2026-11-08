<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/Parameters.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.sinh_scale_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling inequality for hyperbolic sine

**Claim.** If $0\le a\le1$ and $u\ge0$, then $\sinh(au)\le a\sinh u$.

**Proof.** The function $\sinh$ is convex on the nonnegative half-line: its derivative is $\cosh$, which is increasing there. Express $au$ as the convex combination $a u+(1-a)0$. Convexity gives $\sinh(au)\le a\sinh u+(1-a)\sinh0=a\sinh u$.
