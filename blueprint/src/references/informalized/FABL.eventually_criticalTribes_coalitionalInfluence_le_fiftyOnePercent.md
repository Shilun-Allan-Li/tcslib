<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.eventually_criticalTribes_coalitionalInfluence_le_fiftyOnePercent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small coalitions have bounded influence

**Claim.** For all sufficiently large $w$, every coalition of size at most $d/(800\log d)$ has coalitional influence at most $51/100$, where $d$ is the critical tribes dimension.

**Proof.** Take $w$ large enough that $w\ge1$, $d>1$, $2^{-w}\le2\log d/d$, and $\log d/d<1/800$. If $|J|\le d/(800\log d)$, multiply the coalition-size bound by the nonnegative estimate for $2^{-w}$. This gives $|J|2^{-w}\le1/400$. The separate critical tribes estimate bounds the influence by $1/2+(|J|+1)2^{-w}$ ($\texttt{coalitionalInfluence\_criticalTribes\_le\_half\_add\_succ\_card\_mul\_inv\_pow$). The extra $2^{-w}$ is at most $2\log d/d<1/400$, so the resulting bound is strictly less than $1/2+1/400+1/400=51/100$.

**Key facts.** `FABL.eventually_inv_two_pow_le_two_mul_log_dimension_div_dimension`, `FABL.tendsto_log_tribesCriticalDimension_div_dimension_zero`, `FABL.tendsto_tribesCriticalDimension_atTop`, `FABL.criticalTribesCoalitionConstant_pos`, `FABL.coalitionalInfluence_criticalTribes_le_half_add_succ_card_mul_inv_pow`.
