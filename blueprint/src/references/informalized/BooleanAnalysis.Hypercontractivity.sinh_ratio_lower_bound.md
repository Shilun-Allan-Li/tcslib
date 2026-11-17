<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.sinh_ratio_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound for a hyperbolic sine ratio

**Claim.** If $0<a\leq b$, then $\frac{a}{b}e^{a-b}\leq\frac{\sinh a}{\sinh b}$.

**Proof.** Since $0<a\leq b$, the weight $t=a/b$ lies in $[0,1]$. Convexity of the exponential, applied between $0$ and $-2b$ with weights $1-t$ and $t$, gives $e^{-2a}\leq(1-t)+t e^{-2b}$. Rearranging yields $t(1-e^{-2b})\leq1-e^{-2a}$. Use $\sinh x=\frac{e^x}{2}(1-e^{-2x})$ for $x=a,b$; the rearranged inequality, multiplied by the positive factor $e^a/2$, gives the desired comparison after division by $\sinh b>0$.
