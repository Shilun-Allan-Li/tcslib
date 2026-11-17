<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.criticalTribes_towardTrue_max_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Maximum Coalitional Influence

**Claim.** For $w>0$, every set of at most $w$ coordinates has coalitional influence toward $-1$ at most $1/2+d_w$, and there is a set of exactly $w$ coordinates attaining this bound.

**Proof.** For the upper bound, the coalitional influence theorem bounds the influence of any set by one minus the probability that the function already equals $-1$. That probability is $1/2-d_w$, giving the asserted bound. For equality, positivity of the critical tribes size allows choosing a block index. Take the coordinates of that block: the block-coordinate set has size exactly $w$, and its influence is $(1-2^{-w})^{s}-1/2$ with $s$ the critical tribes size. The deficit identity identifies this quantity with $d_w$, so the influence equals $1/2+d_w$.

**Key facts.** `FABL.coalitionalInfluenceToward_le_complement_probability`, `FABL.tribesCritical_neg_one_probability_eq_half_sub_deficit`, `FABL.tribesCriticalSize_pos`, `FABL.card_tribesBlockCoordinates`, `FABL.coalitionalInfluenceToward_tribes_block_neg_one`, `FABL.tribesCriticalProbabilityDeficit_eq_pow`.
