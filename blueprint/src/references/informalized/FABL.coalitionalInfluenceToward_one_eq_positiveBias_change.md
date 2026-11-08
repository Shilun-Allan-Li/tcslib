<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_one_eq_positiveBias_change -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Influence as a Bias Change

**Claim.** For a monotone Boolean function, its coalitional influence toward $+1$ equals the positive bias of the bribed function minus the positive bias of the original function.

**Proof.** By the mean-change identity, the influence is half the difference between the mean of the bribed function and the original mean (`coalitionalInfluenceToward_one_eq_mean_change`). Each positive bias is half of one plus the corresponding mean (`positiveBias_eq_mean`). Substituting these expressions cancels the constant terms, leaving exactly half the difference of the means.

**Key facts.** `FABL.coalitionalInfluenceToward_one_eq_mean_change`, `FABL.positiveBias_eq_mean`.
