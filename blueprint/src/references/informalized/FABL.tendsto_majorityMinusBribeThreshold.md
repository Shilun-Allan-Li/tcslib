<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majorityMinusBribeThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Minus-Bribe Threshold Limit

**Claim.** If $m(q)\to\infty$ and $k(q)/\sqrt{m(q)}\to t$, then $(k(q)-1)/\sqrt{m(q)}\to t$.

**Proof.** Because $m(q)\to\infty$, its square root does too, and its reciprocal tends to zero. Subtracting this vanishing reciprocal from the assumed limit $k(q)/\sqrt{m(q)}\to t$ still gives limit $t$. For all sufficiently large $q$, $m(q)>0$, and then
\[\frac{k(q)-1}{\sqrt{m(q)}}=\frac{k(q)}{\sqrt{m(q)}}-\frac{1}{\sqrt{m(q)}}.\]
Thus the expression in the claim agrees eventually with the difference just shown to converge to $t$.
