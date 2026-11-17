<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.levy_bound_of_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimized scale bound

**Claim.** If $B\ge0$ and $L\le (m+2)\eta+(2^m/\eta^{m+1})B$ for every $\eta>0$, then $L\le((m+2)+2^m)B^{1/(m+2)}$.

**Proof.** Split into the cases $B=0$ and $B>0$. If $B=0$, the target right-hand side is zero. Given any $\delta>0$, choose $\eta=\delta/(m+2)$; since $m+2>0$, this is positive, and the scale hypothesis gives $L\le\delta$. Holding for every positive $\delta$, this implies $L\le0$. If $B>0$, choose $\eta=B^{1/(m+2)}>0$. Then $\eta^{m+2}=B$, so the second term in the scale bound becomes $2^m\eta$: indeed, $B/\eta^{m+1}=\eta$. The bound is therefore $L\le((m+2)+2^m)\eta$, which is the claimed expression.
