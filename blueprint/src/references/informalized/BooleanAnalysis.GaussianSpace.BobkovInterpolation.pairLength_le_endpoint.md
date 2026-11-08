<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairLength_le_endpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric endpoint length comparison

**Claim.** Under the stated hypotheses on $P$, for $a+b,a-b,t\in[0,1]$ and $c\ge0$, one has $L(t,c)\le L(1,c+b^2(1-t^2))$.

**Proof.** 1. Regard the difference between the length at $(t,c)$ and its endpoint comparison length as a deficit on the domain $[0,1]\times[0,\infty)$. Continuity of $P$ on $[0,1]$ ensures that this deficit is bounded above on that domain (the bound is supplied by `bddAbove_pairDeficit`).

2. The half-step estimate (`pairDeficit_half_step`) says that at any $(r,d)$ in the domain, the deficit is at most half the deficit at $\bigl(|2r-1|,d+((1-r)b)^2\bigr)$. This new point remains in the domain: if $0\le r\le1$, then $|2r-1|\le1$, and the second coordinate is nonnegative.

3. A bounded-above function on this domain that admits such a half-step at every point is nonpositive everywhere (`nonpos_of_bddAbove_of_half_step`). Thus the deficit at $(t,c)$ is nonpositive, which is precisely the asserted endpoint comparison.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.bddAbove_pairDeficit`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.nonpos_of_bddAbove_of_half_step`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.pairDeficit_half_step`.
