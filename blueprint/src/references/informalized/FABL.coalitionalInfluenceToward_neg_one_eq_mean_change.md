<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluenceToward_neg_one_eq_mean_change -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Influence as a Mean Change

**Claim.** For a monotone Boolean function, the coalitional influence toward $-1$ equals half the difference between the mean of the original function and the mean after setting the coordinates in $J$ to $-1$.

**Proof.** Monotonicity gives the pointwise characterization that a coalition can attain $-1$ precisely when the function obtained by setting its coordinates to $-1$ already equals $-1` (`coalitionCanAttain_neg_one_iff_bribe_neg_one`). Thus the coalition success probability is the probability that the bribed function equals $-1$. For each Boolean function, its mean is the probability of output $1$ minus the probability of output $-1$ (`mean_eq_probability_one_sub_probability_neg_one`), and these two probabilities sum to $1` (`uniformProbability_one_add_neg_one_eq_one`). Applying these identities to the original and bribed functions, and substituting into the definition of influence, gives half the original mean minus the bribed mean.

**Key facts.** `FABL.coalitionCanAttain_neg_one_iff_bribe_neg_one`, `FABL.mean_eq_probability_one_sub_probability_neg_one`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
