<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluence_criticalTribes_le_half_add_succ_card_mul_inv_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Tribes Influence Bound

**Claim.** For $w>0$, the coalitional influence of the critical tribes function on any coordinate set $J$ is at most $\tfrac12+(|J|+1)2^{-w}$.

**Proof.** Decompose the coalitional influence into its contributions toward $1$ and toward $-1$ using the directional decomposition theorem (`FABL.coalitionalInfluence_eq_toward_add_toward`). For the first contribution, the bound for critical tribes gives at most $|J|2^{-w}$: apply `FABL.coalitionalInfluenceToward_criticalTribes_one_le` with $k=|J|$. For the second, directional influence is bounded by one minus the probability that the function already equals the target (`FABL.coalitionalInfluenceToward_le_complement_probability`). The probability of output $-1$ for critical tribes is $\tfrac12-D_w$, where $D_w$ is the critical probability deficit (`FABL.tribesCritical_neg_one_probability_eq_half_sub_deficit`). The deficit lies between $0$ and $2^{-w}$ (`FABL.tribesCriticalProbabilityDeficit_mem_Icc`), so this second contribution is at most $\tfrac12+D_w\le \tfrac12+2^{-w}$. Adding the two bounds yields the result.

**Key facts.** `FABL.coalitionalInfluence_eq_toward_add_toward`, `FABL.coalitionalInfluenceToward_criticalTribes_one_le`, `FABL.coalitionalInfluenceToward_le_complement_probability`, `FABL.tribesCritical_neg_one_probability_eq_half_sub_deficit`, `FABL.tribesCriticalProbabilityDeficit_mem_Icc`.
