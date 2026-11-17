<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.eventually_totalInfluence_tribesCritical_eq_log_dimension_mul_one_add_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Total Influence Identity

**Claim.** Eventually, the total influence of the critical tribes function equals $\log D_w$ times $1$ plus the relative error in its coordinate influence.

**Proof.** Restrict to $w\ge 1$ and to dimensions $D_w>1$, which holds eventually because the critical dimension tends to infinity. The exact total-influence formula for critical tribes then identifies the total influence with $D_w$ times the coordinate influence. Since $\log D_w\ne0$, substituting the definition of the relative error and simplifying yields $\log D_w(1+e_w)=D_w$ times that coordinate influence, as required.

**Key facts.** `FABL.tendsto_tribesCriticalDimension_atTop`, `FABL.totalInfluence_tribesCritical`.
