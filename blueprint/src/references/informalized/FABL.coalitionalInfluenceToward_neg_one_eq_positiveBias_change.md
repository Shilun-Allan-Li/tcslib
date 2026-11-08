<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_neg_one_eq_positiveBias_change -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Influence as a Positive Bias Change

**Claim.** For a monotone Boolean function, its influence toward $-1$ equals its positive bias minus the positive bias after setting the coordinates in $J$ to $-1$.

**Proof.** The mean-change identity expresses this influence as half the original mean minus the bribed mean (`coalitionalInfluenceToward_neg_one_eq_mean_change`). Positive bias is one half of one plus the mean (`positiveBias_eq_mean`). Expressing both means in terms of their positive biases makes the half-difference exactly the original positive bias minus the bribed positive bias.

**Key facts.** `FABL.coalitionalInfluenceToward_neg_one_eq_mean_change`, `FABL.positiveBias_eq_mean`.
