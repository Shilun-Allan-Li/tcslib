<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.fourierCoeff_tribes_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-frequency coefficient of tribes

**Claim.** The Fourier coefficient of the tribes function at the empty set is $2(1-2^{-w})^s-1$.

**Proof.** The empty-frequency coefficient equals the mean (`FABL.mean_eq_fourierCoeff_empty`). For a Boolean function, that mean is the probability of output $1$ minus the probability of output $-1$ (`FABL.mean_booleanFunction_eq_prob_one_sub_prob_neg_one`). The probability of output $-1$ for tribes is $1-(1-2^{-w})^s$ (`FABL.tribes_neg_one_probability`), while the probabilities of the two possible outputs sum to $1$ (`FABL.uniformProbability_one_add_neg_one_eq_one`). Hence the probability of output $1$ is $(1-2^{-w})^s$, and subtracting the probability of output $-1$ gives $2(1-2^{-w})^s-1$.

**Key facts.** `FABL.mean_eq_fourierCoeff_empty`, `FABL.mean_booleanFunction_eq_prob_one_sub_prob_neg_one`, `FABL.tribes_neg_one_probability`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
