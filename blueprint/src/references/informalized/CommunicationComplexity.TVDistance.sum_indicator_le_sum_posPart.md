<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.sum_indicator_le_sum_posPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator sum bounded by positive parts

**Claim.** For a finite type $\alpha$, a real-valued function $a$ on $\alpha$, and any subset $S$, the sum of $a(x)$ over points in $S$ is at most the sum over all points of $\max(a(x),0)$.

**Proof.** Compare the summands pointwise. If $x\in S$ and $a(x)\ge 0$, the two summands agree. If $x\in S$ and $a(x)<0$, the indicator summand is negative while the positive-part summand is zero. If $x\notin S$, the indicator summand is zero, which is at most $\max(a(x),0)$. Thus every indicator summand is bounded by its corresponding positive part, and summing these inequalities proves the result.
