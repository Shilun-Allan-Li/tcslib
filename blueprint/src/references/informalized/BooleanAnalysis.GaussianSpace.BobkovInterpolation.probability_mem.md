<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.probability_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability along a symmetric segment

**Claim.** If $a+b,a-b\in[0,1]$ and $-1\le t\le1$, then $a+tb\in[0,1]$.

**Proof.** Write $a+tb$ as the convex combination of $a+b$ and $a-b$ with weights $(1+t)/2$ and $(1-t)/2$. The bounds on $t$ make both weights nonnegative, and they sum to one. Since the interval $[0,1]$ is convex and both endpoints lie in it, their convex combination also lies in it.
