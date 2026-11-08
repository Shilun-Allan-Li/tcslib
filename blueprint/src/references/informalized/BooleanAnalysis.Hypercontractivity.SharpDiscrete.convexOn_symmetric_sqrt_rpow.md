<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointCalculus.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.convexOn_symmetric_sqrt_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of Symmetric Square Root Powers

**Claim.** For $1<p<2$, the function $z\mapsto(1+\sqrt z)^p+(1-\sqrt z)^p$ is convex on $[0,1]$.

**Proof.** On the interior $0<z<1$, define
\[
d_1(z)=\frac p2\,\frac{(1+\sqrt z)^{p-1}-(1-\sqrt z)^{p-1}}{\sqrt z}.
\]
Differentiating the function in the claim gives $d_1$; differentiating $d_1$ gives
\[
d_2(z)=\frac{p}{4(\sqrt z)^3}\left((p-1)\sqrt z\bigl((1+\sqrt z)^{p-2}+(1-\sqrt z)^{p-2}\bigr)-\bigl((1+\sqrt z)^{p-1}-(1-\sqrt z)^{p-1}\bigr)\right).
\]
The symmetric power slope inequality (`symmetric_power_slope_le`), applied with $t=\sqrt z\in(0,1)$, says the bracket in this expression is nonnegative. Its prefactor is positive, so $d_2(z)\ge0$. The function is continuous on the closed interval, and its first and second derivatives exist in the interior as just computed. The second-derivative criterion for convexity on an interval therefore gives convexity on $[0,1]$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.symmetric_power_slope_le`.
