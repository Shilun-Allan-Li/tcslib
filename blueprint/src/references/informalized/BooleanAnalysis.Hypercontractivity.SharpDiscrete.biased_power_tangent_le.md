<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointCalculus.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_power_tangent_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tangent Bound for a Biased Power

**Claim.** For $1<p<2$, $0<t<1$, and $0\le z\le1$, the biased power expression at $z$ is bounded below by its tangent line at $t^2$, with the stated slope.

**Proof.** Let
\[
f(x)=\bigl((1+\sqrt{x})^p+(1-\sqrt{x})^p\bigr)^{2/p},
\]
and let $d$ be the slope displayed in the claim. The point $t^2$ and the point $z$ both belong to $[0,1]$. Differentiating at $t^2$, using $\sqrt{t^2}=t$ since $t>0$, gives $f'(t^2)=d$: the derivative of $\sqrt{x}$ there is $1/(2t)$, and the chain and power rules yield the stated expression. By convexity of $f$ on $[0,1]$ (`convexOn_biased_power`), its graph lies above the tangent line at this interior point. Thus $f(t^2)+d(z-t^2)\le f(z)$, which is precisely the desired inequality after substituting the definitions of $f$ and $d$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.convexOn_biased_power`.
