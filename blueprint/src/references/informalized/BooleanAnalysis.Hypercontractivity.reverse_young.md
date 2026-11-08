<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Holder.lean :: BooleanAnalysis.Hypercontractivity.reverse_young -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reverse Young inequality

**Claim.** If $0<r<1$, $a\ge0$, and $b>0$, then $ab\ge a^r/r+b^{r/(r-1)}/(r/(r-1))$.

**Proof.** Let $t=a/b^{1/(r-1)}$, which is nonnegative. The tangent-line bound for the concave power $t^r$ at $t=1$ gives $t^r\le1+r(t-1)$. Substituting $a=t b^{1/(r-1)}$ and using the laws of real powers rewrites this as $a^r=t^r b^{r/(r-1)}$ and $ab=t b^{r/(r-1)}$. The tangent-line inequality, multiplied by the positive factor $b^{r/(r-1)}/r$, then rearranges to the claimed reverse Young inequality.
