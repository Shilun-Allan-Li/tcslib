<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointCalculus.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.convexOn_biased_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of a Biased Power Expression

**Claim.** For $1<p<2$, the function $z\mapsto\bigl((1+\sqrt z)^p+(1-\sqrt z)^p\bigr)^{2/p}$ is convex on $[0,1]$.

**Proof.** Write $g(z)=(1+\sqrt z)^p+(1-\sqrt z)^p$. The symmetric square-root power function $g$ is convex on $[0,1]$ (`convexOn_symmetric_sqrt_rpow`). It is also nonnegative there, since $0\le\sqrt z\le1$ makes both bases nonnegative. The exponent $2/p$ is at least $1$, because $p<2$ and $p>0$. The function $s\mapsto s^{2/p}$ is increasing on nonnegative inputs and convex for an exponent at least $1$. Applying monotonicity to the convexity inequality for $g$, and then applying convexity of this power function to the resulting weighted average, proves convexity of $g^{2/p}$ on the interval.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.convexOn_symmetric_sqrt_rpow`.
