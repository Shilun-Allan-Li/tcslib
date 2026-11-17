<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.lowDegree_norm_le_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low degree reverse norm bound

**Claim.** If $f$ has degree at most $k$ and $1\le p\le2$, then $\|f\|_2\le \exp((2/p-1)k)\|f\|_p$.

**Proof.** When $p=2$, the result is equality. Otherwise $1\le p<2$. For each $q>2$, the auxiliary estimate bounds $\|f\|_2$ by $\exp(kq(2-p)/(2p))\|f\|_p$. Regard the right-hand side as a continuous function of $q$ and let $q$ tend to $2$ from above. The inequality passes to the limit, giving the same bound with exponent $k(2-p)/p$. Since $(2-p)/p=2/p-1$, this is the desired estimate.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lowDegree_norm_le_two_aux`.
