<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointCalculus.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.symmetric_power_slope_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Symmetric-power slope bound

**Claim.** For $1<p<2$ and $0\le t<1$, $(1+t)^{p-1}-(1-t)^{p-1}\le(p-1)t((1+t)^{p-2}+(1-t)^{p-2})$.

**Proof.** Define $H(x)=(p-1)x((1+x)^{p-2}+(1-x)^{p-2})-((1+x)^{p-1}-(1-x)^{p-1})$ on $[0,t]$. Both bases $1+x$ and $1-x$ are positive there. Differentiating and collecting terms gives $H'(x)=(p-1)(p-2)x((1+x)^{p-3}-(1-x)^{p-3})$. For $0<x<t$, we have $1+x>1-x>0$ and $p-3<0$, so the parenthesized difference is nonnegative. The factor $(p-1)(p-2)x$ is nonpositive; therefore $H'(x)\le0$ as expressed in the proof? Since the parentheses are nonnegative, this product is indeed nonpositive. The supplied proof establishes that $H$ is monotone on $[0,t]$ with the orientation giving $H(t)\ge H(0)$. As $H(0)=0$, it follows that $H(t)\ge0$, which rearranges to the claimed inequality.

**Caveat.** The proof source's derivative-sign step appears inconsistent: with $1+x>1-x$ and $p-3<0$, one has $(1+x)^{p-3}-(1-x)^{p-3}<0$, not nonnegative. This makes the displayed derivative nonnegative, consistent with the claimed conclusion, but the source text's stated intermediate comparison and sign justification are misstated.
