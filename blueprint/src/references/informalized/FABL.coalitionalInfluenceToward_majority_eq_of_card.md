<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_majority_eq_of_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Depends on Coalition Size

**Claim.** For majority, coalitions of equal cardinality have the same coalitional influence toward either sign.

**Proof.** Every sign is either $1$ or $-1$, so consider these targets separately. Majority is monotone (`majority_monotone`). For target $1$, its coalitional influence is half the increase in mean caused by bribing the coalition to $1 (`coalitionalInfluenceToward_one_eq_mean_change`). For target $-1$, it is half the decrease in mean caused by bribing the coalition to $-1 (`coalitionalInfluenceToward_neg_one_eq_mean_change`). In either case, `mean_bribeFunction_majority_eq_of_card` says that the bribed majority means for the two coalitions agree when their cardinalities agree. The original majority mean is common to both, so the corresponding influences are equal.

**Key facts.** `FABL.majority_monotone`, `FABL.coalitionalInfluenceToward_one_eq_mean_change`, `FABL.mean_bribeFunction_majority_eq_of_card`, `FABL.coalitionalInfluenceToward_neg_one_eq_mean_change`.
