<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.weighted_negative_moment_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted negative-moment inequality

**Claim.** Under the stated scalar inequality and assumptions on the weights, the weighted negative moment around the weighted mean is at most the weighted moment of the original values.

**Proof.** Let $a=\sum_{i\in s}w_iF_i$ and set $k=q(1+c)|a|^q/a$. The scalar affine inequality `CenteredContraction.scalar_affine`, applied with center $a$ and displacement $F_i-a$, gives $|a-c(F_i-a)|^q\le |F_i|^q-k(F_i-a)$; here $a+(F_i-a)=F_i$. Multiplication by $w_i\ge0$ preserves this inequality, so summing over $i$ bounds the left-hand side by $\sum_i w_i|F_i|^q-k\sum_iw_i(F_i-a)$. The latter centered sum vanishes: using $\sum_iw_i=1$, it equals $\sum_iw_iF_i-a\sum_iw_i=a-a=0$. This proves the desired bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_affine`.
