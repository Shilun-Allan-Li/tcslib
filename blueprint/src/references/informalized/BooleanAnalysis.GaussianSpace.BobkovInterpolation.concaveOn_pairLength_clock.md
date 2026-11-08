<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.concaveOn_pairLength_clock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concavity in the Clock Variable

**Claim.** For every choice of the profile and vectors, the function $c\mapsto L(1,c)$ is concave on $[0,\infty)$.

**Proof.** For any fixed $K\ge0$, the function $c\mapsto\sqrt{K+c}$ is concave on $[0,\infty)$: apply concavity of the square root to the nonnegative numbers $K+x$ and $K+y$, whose convex combination is $K+(\alpha x+\beta y)$. At $t=1$, each radicand in $L(1,c)$ has the form $K+c$, with $K=P(a\pm b)^2+\sum_j(u_j\pm v_j)^2\ge0$. The two resulting square-root functions are concave, and their average is concave as well. This average is exactly $L(1,c)$.
