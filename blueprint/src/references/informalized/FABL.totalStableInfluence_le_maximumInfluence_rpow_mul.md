<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.totalStableInfluence_le_maximumInfluence_rpow_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable influence upper bound

**Claim.** Under the stated assumptions on $\delta$ and $\rho$, total stable influence is at most the maximum coordinate influence to the power $\delta$, multiplied by total influence.

**Proof.** For each coordinate $i$, the coordinatewise stable-influence estimate (\texttt{stableInfluence\_le\_booleanInfluence\_rpow}) bounds its stable influence by $\operatorname{Inf}_i(f)^{2/(1+\rho)}$. The exponent relation makes this $\operatorname{Inf}_i(f)^{1+\delta}$. Since coordinate influence is nonnegative and at most the maximum influence (\texttt{influence\_nonneg}, \texttt{booleanInfluence\_le\_maximumInfluence}), monotonicity of the nonnegative real power gives $\operatorname{Inf}_i(f)^\delta\le \operatorname{Inf}_{\max}(f)^\delta$. Multiplying by the nonnegative coordinate influence yields the bound $\operatorname{Inf}_i(f)^{1+\delta}\le \operatorname{Inf}_{\max}(f)^\delta\operatorname{Inf}_i(f)$. If the coordinate influence is zero, the same inequality follows directly; otherwise the factorization of the $(1+\delta)$-power gives it. Summing over coordinates proves the desired estimate. The equality between Boolean influence and sign-representation influence (\texttt{booleanInfluence\_eq\_influence\_toReal}) identifies the summed coordinate influences with total influence. Nonnegativity of the maximum influence (\texttt{maximumInfluence\_nonneg}) ensures its power is well-defined for the stated exponent.

**Key facts.** `FABL.stableInfluence_le_booleanInfluence_rpow`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`, `FABL.booleanInfluence_le_maximumInfluence`, `FABL.maximumInfluence_nonneg`.
