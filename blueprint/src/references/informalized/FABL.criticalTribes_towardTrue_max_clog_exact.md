<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.criticalTribes_towardTrue_max_clog_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Maximum Influence Under a Logarithmic Size Bound

**Claim.** For $w\ge4$, every set of at most $\lceil\log_2 N_w\rceil$ coordinates has coalitional influence toward $-1$ at most $1/2+d_w$, and some set of exactly $w$ coordinates attains this bound.

**Proof.** For any coordinate set $J$, its coalitional influence toward $-1$ is at most one minus the probability that the function already equals $-1$. The probability identity expresses that probability as $1/2-d_w$, so the influence is at most $1/2+d_w$, regardless of the size of $J$. For attainment, the exact maximum theorem supplies a set of exactly $w$ coordinates whose influence equals $1/2+d_w$. The dimension bound $w\le\lceil\log_2 N_w\rceil$ then shows that this witness satisfies the required size constraint.

**Key facts.** `FABL.coalitionalInfluenceToward_le_complement_probability`, `FABL.tribesCritical_neg_one_probability_eq_half_sub_deficit`, `FABL.criticalTribes_towardTrue_max_exact`, `FABL.width_le_clog_tribesCriticalDimension`.
