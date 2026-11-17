<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majorityPlusBribeThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Plus-Bribe Threshold Limit

**Claim.** If $m(q)\to\infty$ and $k(q)/\sqrt{m(q)}\to t$, then $-(k(q)+1)/\sqrt{m(q)}\to -t$.

**Proof.** As $m(q)\to\infty$, the reciprocal of $\sqrt{m(q)}$ tends to zero. Negating the assumed convergent sequence gives limit $-t$; subtracting that vanishing reciprocal leaves the same limit. Eventually $m(q)>0$, and for those indices
\[ -\frac{k(q)+1}{\sqrt{m(q)}}=-\frac{k(q)}{\sqrt{m(q)}}-\frac{1}{\sqrt{m(q)}}.\]
This identifies the expression in the claim with the sequence whose limit was just established.
