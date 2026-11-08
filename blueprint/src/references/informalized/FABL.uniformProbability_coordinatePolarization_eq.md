<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.uniformProbability_coordinatePolarization_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization preserves output probabilities

**Claim.** Coordinate polarization preserves the uniform probability of either sign output: for each $b\in\{-1,1\}$, the probability that the polarized function equals $b$ is the same as the probability that the original function equals $b$.

**Proof.** It suffices to consider the two possible outputs. The mean of a sign-valued function equals the probability of output $1$ minus the probability of output $-1$ (\texttt{FABL.mean_eq_probability_one_sub_probability_neg_one}), and those two probabilities sum to $1$ (\texttt{FABL.uniformProbability_one_add_neg_one_eq_one}). Polarization preserves the mean (\texttt{FABL.mean_coordinatePolarization}). Consequently, the original and polarized functions have the same difference and the same sum of their two output probabilities. These two linear equations determine each probability individually, proving equality for both signs.

**Key facts.** `FABL.mean_eq_probability_one_sub_probability_neg_one`, `FABL.uniformProbability_one_add_neg_one_eq_one`, `FABL.mean_coordinatePolarization`.
