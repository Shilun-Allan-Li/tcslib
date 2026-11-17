<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluenceToward_one_eq_mean_change -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Influence as a Mean Change

**Claim.** For a monotone Boolean function, its coalitional influence toward $+1$ equals half the increase in its mean after setting the coalition's coordinates to $+1$.

**Proof.** Monotonicity gives the characterization that the coalition can attain $+1$ from $x$ exactly when the function evaluated after setting every coordinate in $J$ to $+1$ is $+1$ (`coalitionCanAttain_one_iff_bribe_one`). Hence the coalition success probability is the positive-output probability of the bribed function. For any Boolean function, its mean is the probability of output $+1$ minus the probability of output $-1$ (`mean_eq_probability_one_sub_probability_neg_one`), and those two probabilities sum to one (`uniformProbability_one_add_neg_one_eq_one`). Consequently the probability of output $+1$ is one half of one plus the mean. Subtracting the original positive-output probability from the bribed one cancels the constant terms and yields half the difference of their means, as claimed.

**Key facts.** `FABL.coalitionCanAttain_one_iff_bribe_one`, `FABL.mean_eq_probability_one_sub_probability_neg_one`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
