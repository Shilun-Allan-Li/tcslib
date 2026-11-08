<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.booleanInfluence_bribeFunction_tribes_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound for Bribed Tribes

**Claim.** For tribes with block width $w$ and $s$ blocks, after coordinates in $J$ are set to $+1$, the influence of any coordinate is at most $1/2^{w-1}$.

**Proof.** Split into whether $i\in J$. If so, the influence is zero by the result that a bribed coordinate has zero influence, and the desired bound is nonnegative. If $i\notin J$, every pivotal input for the bribed tribes function satisfies the event that the rest of the relevant block is true (`FABL.isPivotal_bribeFunction_tribes_imp_restTrue`). Inclusion of events bounds the uniform probability of being pivotal by the probability of this rest-true event (`FABL.uniformProbability_mono`). That event has probability exactly $1/2^{w-1}$ (`FABL.uniformProbability_tribesRestTrue`), yielding the bound.

**Key facts.** `FABL.booleanInfluence_bribeFunction_eq_zero_of_mem`, `FABL.isPivotal_bribeFunction_tribes_imp_restTrue`, `FABL.uniformProbability_mono`, `FABL.uniformProbability_tribesRestTrue`.
