<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.criticalTribes_towardTrue_excess_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Tribes Probability Excess Bound

**Claim.** As $w\to\infty$, the excess $(1/2+d_w)-1/2$ is $O(\log(N_w)/N_w)$, where $N_w$ is the critical tribes dimension and $d_w$ is its probability deficit.

**Proof.** The probability deficit theorem gives $d_w=O(\log(N_w)/N_w)$. Since $(1/2+d_w)-1/2=d_w$ for every $w$, the same asymptotic bound holds for the stated excess.

**Key facts.** `FABL.tribesCriticalProbabilityDeficit_isBigO_log_dimension_div_dimension`.
