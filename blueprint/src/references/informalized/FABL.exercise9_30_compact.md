<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.exercise9_30_compact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compact maximum-influence bound

**Claim.** For a Boolean function of positive variance and $0<\delta<1$, with $I$ its total influence, $V$ its variance, and $\rho=(1-\delta)/(1+\delta)$, one has $\bigl(\rho^{I/V-1}/(I/V)\bigr)^{1/\delta}\le\max_i\operatorname{Inf}_i(f)$.

**Proof.** Set $K=I/V$ and $M$ equal to the maximum influence. Since variance is at most total influence (`variance_le_totalInfluence`), $K\ge1$ and in particular is positive. The ratio parameter lies in $(0,1]$ (`exercise9_30Rho_mem_Ioc`), and its defining formula gives the exponent identity $2/(1+\rho)=1+\delta$ (`exercise9_30_exponent_identity`). The variance-versus-stable-influence bound gives $V\rho^{K-1}\le\operatorname{Stab}_\rho(f)$ (`variance_mul_rho_rpow_sub_one_le_totalStableInfluence`), while the stable-influence upper bound gives $\operatorname{Stab}_\rho(f)\le M^\delta I$ (`totalStableInfluence_le_maximumInfluence_rpow_mul`). Combine them and cancel the positive factor $V$, using $I=KV$, to obtain $\rho^{K-1}/K\le M^\delta$. To take the $1/\delta$ power and recover $M$, note that $M>0$: the edge lower bound (`edgeKKL`) makes it strictly positive when $V>0$. Monotonicity of nonnegative real powers now yields $(\rho^{K-1}/K)^{1/\delta}\le(M^\delta)^{1/\delta}=M$, which is the assertion.

**Key facts.** `FABL.variance_le_totalInfluence`, `FABL.exercise9_30Rho_mem_Ioc`, `FABL.exercise9_30_exponent_identity`, `FABL.variance_mul_rho_rpow_sub_one_le_totalStableInfluence`, `FABL.totalStableInfluence_le_maximumInfluence_rpow_mul`, `FABL.edgeKKL`.
