<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.continuousOn_pairLength_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Pair Length

**Claim.** If $P$ is continuous on $[0,1]$ and both endpoints $a+b$ and $a-b$ lie there, then $t\mapsto L(t,0)$ is continuous on $[0,1]$.

**Proof.** For $t\in[0,1]$, the point $a+tb$ lies in $[0,1]$ by the endpoint interpolation fact (`probability_mem`). Thus composing $P$ with this affine map gives a continuous function on the interval. The same fact applied to $-t$ shows that $a-tb$ also stays in $[0,1]$, so the other composition is continuous too. Squaring these functions, adding the continuous sums of squares, taking square roots, and averaging preserves continuity. The resulting expression is precisely $L(t,0)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.probability_mem`.
